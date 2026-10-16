import InitECandidate.Runtime.MemzeroSyntax
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def memcpyAddress (name : MlS) : ExpHOL 64 :=
  .op .add [.var .local name,.var .local (ofString "i")]

def memcpyWord8Body : ProgHOL 64 :=
  .seq (.store (memcpyAddress (ofString "dst")) (.load .one (memcpyAddress (ofString "src")))) (memzeroAdvance 8)

def memcpyDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_memcpy with | .function fn => fn.body | _ => .skip

def memcpyWord32Loop : ProgHOL 64 :=
  match memcpyDecodedBody with | .dec _ _ _ (.seq (.ite _ (.seq loop _) _) _) => loop | _ => .skip

def memcpyAlignmentCondition : ExpHOL 64 :=
  .cmp .equal (.op .and [.op .or [.var .local (ofString "dst"),.var .local (ofString "src")],.const 7]) (.const 0)

def memcpyAfterAligned : ProgHOL 64 :=
  match memcpyDecodedBody with | .dec _ _ _ (.seq _ rest) => rest | _ => .skip

theorem source_memcpy_word8 : sourceFunctionBody Guest.guestFn_memcpy =
    .dec (ofString "i") .one (.const 0)
      (.seq (.ite memcpyAlignmentCondition
        (.seq memcpyWord32Loop (.while (memzeroBlockCondition 8) memcpyWord8Body)) .skip) memcpyAfterAligned) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

theorem eval_memcpyAddress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer index : BitVec 64)
    (pointerLocal : state.locals.lookup name = some (.val (.word pointer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (memcpyAddress name) = some (.val (.word (pointer + index))) := by
  simp [memcpyAddress,evalHOLExact,evalListHOLExact,pointerLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

/-- One actual original word-copy iteration loads before storing and advances
its counter by8, with no source clocks or nonmemory/nonlocal effects. -/
theorem evaluate_memcpy_word8_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index value : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index))
    (sourceDomain : state.memaddrs (source + index)) (cell : state.memory (source + index) = .word value) :
    evaluateHOLFiniteState state memcpyWord8Body =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 8)))
        (sourceWriteWord state (destination + index) value)) := by
  have sourceAddress := eval_memcpyAddress state (ofString "src") source index srcLocal indexLocal
  have destinationAddress := eval_memcpyAddress state (ofString "dst") destination index dstLocal indexLocal
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (memcpyAddress (ofString "src"))) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [sourceAddress]
    simp [memLoadHOLExact,sourceDomain,cell]
  have store := evaluate_store_word state (destination + index) value _ _ destinationAddress loaded destinationDomain
  have advance := evaluate_memzero_advance (sourceWriteWord state (destination + index) value) index 8 indexLocal
  unfold memcpyWord8Body
  rw [evaluateHOLFiniteState_seq_line780,store]
  exact advance

/-- A readable word-copy step needs no assumption about source contents or
source/destination overlap. Its exact write preserves unrelated occupancy. -/
theorem evaluate_memcpy_word8_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : state.memaddrs (destination + index)) (sourceDomain : state.memaddrs (source + index)) :
    ∃ post, evaluateHOLFiniteState state memcpyWord8Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 8))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ∀ capacity used : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination + index) →
        hashOccupiedCount capacity (hashOccupancyRead post used) = hashOccupiedCount capacity (hashOccupancyRead state used) := by
  obtain ⟨value,cell⟩ : ∃ value : BitVec 64, state.memory (source + index) = .word value := by
    cases state.memory (source + index) with | word value => exact ⟨value,rfl⟩
  have run := evaluate_memcpy_word8_body state destination source index value dstLocal srcLocal indexLocal
    destinationDomain sourceDomain cell
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · intro capacity used separate
    exact sourceWriteWord_occupancy_preserved state capacity used (destination + index) value separate

#print axioms evaluate_memcpy_word8_step
#print axioms source_memcpy_word8
#print axioms evaluate_memcpy_word8_body
end InitECandidate.Runtime
