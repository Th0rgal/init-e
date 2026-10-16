import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shared_store_no_return {F : Type} (state : PanSemStateExact 64 F)
    [DecidablePred state.shMemaddrs] (word address : BitVec 64) (bytes : Nat) (value : ValueHOL 64) :
    (shMemStoreHOLExact state word address bytes).1 ≠ some (.returned value) := by
  unfold shMemStoreHOLExact
  split <;> split
  all_goals try split
  all_goals simp

theorem evaluate_shared_store_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (address expression : ExpHOL 64) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address expression)).1 ≠ some (.returned value) := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · exact shared_store_no_return state.toExact _ _ _ value
  · simp

theorem evaluate_external_call_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem evaluate_raise_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (exception : MlS) (expression : ExpHOL 64) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.raise exception expression)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem evaluate_sequence_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (value : ValueHOL 64)
    (firstNoReturn : (evaluateHOLFiniteState state first).1 ≠ some (.returned value))
    (secondNoReturn : ∀ next : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState next second).1 ≠ some (.returned value)) :
    (evaluateHOLFiniteState state (.seq first second)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  split
  · exact secondNoReturn _
  · exact firstNoReturn

theorem evaluate_trap_body_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trap_with)).1 ≠ some (.returned value) := by
  rw [source_trap_body]
  unfold trapSourceBody
  apply evaluate_sequence_no_return
  · exact evaluate_shared_store_no_return _ _ _ _ _
  · intro next
    apply evaluate_sequence_no_return
    · exact evaluate_shared_store_no_return _ _ _ _ _
    · intro next
      apply evaluate_sequence_no_return
      · exact evaluate_shared_store_no_return _ _ _ _ _
      · intro next
        apply evaluate_sequence_no_return
        · exact evaluate_external_call_no_return _ _ _ _ _ _ _
        · intro next
          exact evaluate_raise_no_return _ _ _ _

#print axioms evaluate_trap_body_no_return
end InitECandidate.Runtime
