import InitECandidate.Runtime.OriginalMptFailCode
import InitECandidate.Runtime.MptFailBody
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual mpt_fail calls spend one entry tick and cannot fall through or
time out when that tick is available, including missing exception metadata. -/
theorem evaluate_mptFail_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (code : state.code = originalRuntimeCode) (nonzero : state.clock ≠ 0)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word value)]) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [argument]);
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "code",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "mpt_fail") =
      some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_mpt_fail,.one) := by
    rw [code]; exact originalRuntimeCode_mptFail_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFunctionBody Guest.guestFn_mpt_fail) value installed
  have ticks := clockPreserving_of_straightLine _ mptFail_straightLine entry
  have noTimeout := evaluate_straightLine_no_timeout _ mptFail_straightLine entry
  have noReturn := evaluate_mptFail_body_no_return entry
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero]
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_mpt_fail) with
  | mk result post =>
    rw [run] at ticks noTimeout noReturn
    dsimp only at ticks noTimeout noReturn
    have clock : post.clock = state.clock - 1 := ticks
    cases result with
    | none => exact ⟨clock,by simp,by simp⟩
    | some result => cases result <;> simp_all [emptyLocalsHOLFinite]

#print axioms evaluate_mptFail_call_bounded
end InitECandidate.Runtime
