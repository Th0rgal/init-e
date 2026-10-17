import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.OriginalTrapCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shared_store_no_timeout {F : Type} (state : PanSemStateExact 64 F)
    [DecidablePred state.shMemaddrs] (word address : BitVec 64) (bytes : Nat) :
    (shMemStoreHOLExact state word address bytes).1 ≠ some .timeOut := by
  unfold shMemStoreHOLExact
  split <;> split
  all_goals try split
  all_goals simp

theorem evaluate_shared_store_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (address expression : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address expression)).1 ≠ some .timeOut := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · exact shared_store_no_timeout state.toExact _ _ _
  · simp

theorem evaluate_external_call_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem evaluate_raise_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (exception : MlS) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState state (.raise exception expression)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem evaluate_sequence_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64)
    (one : (evaluateHOLFiniteState state first).1 ≠ some .timeOut)
    (two : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next second).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState state (.seq first second)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  split
  · exact two _
  · exact one

/-- The original trap body cannot consume its clock into a source timeout. -/
theorem evaluate_trap_body_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trap_with)).1 ≠ some .timeOut := by
  rw [source_trap_body]
  unfold trapSourceBody
  apply evaluate_sequence_no_timeout
  · exact evaluate_shared_store_no_timeout _ _ _ _
  · intro next
    apply evaluate_sequence_no_timeout
    · exact evaluate_shared_store_no_timeout _ _ _ _
    · intro next
      apply evaluate_sequence_no_timeout
      · exact evaluate_shared_store_no_timeout _ _ _ _
      · intro next
        apply evaluate_sequence_no_timeout
        · exact evaluate_external_call_no_timeout _ _ _ _ _ _
        · intro next
          exact evaluate_raise_no_timeout _ _ _

#print axioms evaluate_trap_body_no_timeout
end InitECandidate.Runtime
