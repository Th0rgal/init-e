import InitECandidate.Runtime.MemcpyWordOffset
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_memcpy_word_frame_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index offset watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index + offset))
    (sourceDomain : state.memaddrs (source + index + offset))
    (separate : watched ≠ destination + index + offset) :
    ∃ post, evaluateHOLFiniteState state (memcpyWordStore offset) = (none,post) ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.memory watched = state.memory watched := by
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
  change (sourceWriteWord state (destination + index + offset) value).memory watched = _
  simp only [sourceWriteWord,if_neg separate]

#print axioms evaluate_memcpy_word_frame_store
end InitECandidate.Runtime
