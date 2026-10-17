import InitECandidate.Runtime.CompactNibbleNonemptyBody
import InitECandidate.Runtime.MptFailCallBound
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty compact paths take the original error call and never enter the
header load or allocator. One source tick suffices, even without exception metadata. -/
theorem evaluate_compactNibble_empty_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧
      evaluated.1 ≠ none ∧ (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have bound := evaluate_mptFail_call_bounded state (.const 5) 5 code (by omega) (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "mpt_fail") [.const 5]
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_compactNibble_body,evaluateHOLFiniteState_seq_line780,check]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) with
  | mk result post =>
    rw [run] at bound noReturn
    dsimp only at bound noReturn
    cases result with
    | none => exact False.elim (bound.2.2 rfl)
    | some stopped => exact ⟨bound.1,bound.2.1,bound.2.2,noReturn⟩

#print axioms evaluate_compactNibble_empty_body
end InitECandidate.Runtime
