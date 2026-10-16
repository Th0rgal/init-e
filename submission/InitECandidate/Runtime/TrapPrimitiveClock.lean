import InitECandidate.Runtime.TrapSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shared_store_exact_clock {F : Type} (state : PanSemStateExact 64 F)
    [DecidablePred state.shMemaddrs] (word address : BitVec 64) (bytes : Nat) :
    (shMemStoreHOLExact state word address bytes).2.clock = state.clock := by
  unfold shMemStoreHOLExact
  split <;> split
  all_goals first | rfl | (split <;> rfl)

theorem evaluate_shared_store_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.clock = state.clock := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · exact shared_store_exact_clock state.toExact _ _ _
  · rfl

theorem evaluate_raise_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (exception : MlS) (value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.raise exception value)).2.clock = state.clock := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> rfl
  · rfl

theorem evaluate_external_call_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).2.clock = state.clock := by
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

#print axioms evaluate_external_call_clock
#print axioms shared_store_exact_clock
#print axioms evaluate_shared_store_clock
#print axioms evaluate_raise_clock
end InitECandidate.Runtime
