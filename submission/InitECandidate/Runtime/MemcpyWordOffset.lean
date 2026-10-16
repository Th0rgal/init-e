import InitECandidate.Runtime.MemcpyWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyOffset (name : MlS) (offset : BitVec 64) : ExpHOL 64 :=
  if offset = 0 then memcpyAddress name
  else .op .add [.var .local name,.var .local (ofString "i"),.const offset]

def memcpyWordStore (offset : BitVec 64) : ProgHOL 64 :=
  .store (memcpyOffset (ofString "dst") offset) (.load .one (memcpyOffset (ofString "src") offset))

theorem eval_memcpyOffset {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer index offset : BitVec 64)
    (binding : state.locals.lookup name = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (memcpyOffset name offset) = some (.val (.word (pointer + index + offset))) := by
  by_cases zero : offset = 0
  · subst offset
    simpa [memcpyOffset] using eval_memcpyAddress state name pointer index binding indexLocal
  · unfold memcpyOffset
    rw [if_neg zero]
    simp [evalHOLExact,evalListHOLExact,binding,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]

/-- A word-copy store at an unrolled offset preserves all locals, consumes no
clocks and preserves every occupancy array separate from its destination. -/
theorem evaluate_memcpy_word_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index offset : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index + offset))
    (sourceDomain : state.memaddrs (source + index + offset)) :
    ∃ post, evaluateHOLFiniteState state (memcpyWordStore offset) = (none,post) ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ capacity used : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination + index + offset) →
        hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) := by
  obtain ⟨value,cell⟩ : ∃ value : BitVec 64, state.memory (source + index + offset) = .word value := by
    cases state.memory (source + index + offset) with | word value => exact ⟨value,rfl⟩
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (memcpyOffset (ofString "src") offset)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_memcpyOffset state (ofString "src") source index offset srcLocal indexLocal]
    simp [memLoadHOLExact,sourceDomain,cell]
  have store := evaluate_store_word state (destination + index + offset) value _ _
    (eval_memcpyOffset state (ofString "dst") destination index offset dstLocal indexLocal) loaded destinationDomain
  refine ⟨_,store,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro capacity used separate
  exact sourceWriteWord_occupancy_preserved state capacity used (destination + index + offset) value separate

#print axioms eval_memcpyOffset
#print axioms evaluate_memcpy_word_store
end InitECandidate.Runtime
