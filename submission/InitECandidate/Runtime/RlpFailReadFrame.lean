import InitECandidate.Runtime.RlpFailBody
import InitECandidate.Runtime.OriginalRlpFailCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDiscardCallFrame
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpFail_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_rlp_fail) = true := by
  rw [source_rlpFail_body]
  rfl

/-- The actual error helper preserves memory and globals at all clocks,
including absent exception metadata and failed return checks. -/
theorem evaluate_rlpFail_call_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word value)]) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [argument])
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  have installed : state.code.lookup (ofString "rlp_fail") =
      some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_rlp_fail,.one) := by
    rw [code]; exact originalRuntimeCode_rlpFail_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "rlp_fail") (ofString "code")
    (sourceFunctionBody Guest.guestFn_rlp_fail) value installed
  apply evaluate_discard_call_frame state (ofString "rlp_fail") [argument] [.val (.word value)]
    (sourceFunctionBody Guest.guestFn_rlp_fail) _ .one args lookup
  intro result post run
  have memory := evaluate_readOnly_memory _ rlpFail_readOnly (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code",.val (.word value))))
  have globals := evaluate_readOnly_globals _ rlpFail_readOnly (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code",.val (.word value))))
  rw [run] at memory globals
  exact ⟨memory,globals⟩

#print axioms evaluate_rlpFail_call_frame
end InitECandidate.Runtime
