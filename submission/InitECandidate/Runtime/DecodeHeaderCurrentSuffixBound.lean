import InitECandidate.Runtime.DecodeHeaderCurrentUintSuffixBound
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem source_decode_header_current_body : decodeHeaderCurrentSuffix =
    headerBytesStep 21 32 232 decodeHeaderCurrentUintSuffix := rfl

/-- All three actual current-header field calls and both record stores finish
within three uniform numeric budgets, including every terminal failure. -/
theorem decode_header_current_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (countBound : 23 ≤ count.toNat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : 3 * (headerRlpFieldCost inputLimit + 35) ≤ s.clock) : RunBounded s decodeHeaderCurrentSuffix (3 * (headerRlpFieldCost inputLimit + 35)) := by
  have first := header_bytes_step_reaches s array count input inputLength scratch frame record ceiling inputLimit
    21 32 232 decodeHeaderCurrentUintSuffix (by decide) atArray atRecord before recordFits table (by simpa using (show 21 < count.toNat by omega))
    above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  rw [← source_decode_header_current_body] at first
  have closed : RunBounded s decodeHeaderCurrentSuffix
      ((headerRlpFieldCost inputLimit + 1) + ((headerRlpFieldCost inputLimit + 1) + (headerRlpFieldCost inputLimit + 35))) := by
    apply RunBounded.ofReaches (by omega) first
    intro next facts remaining
    obtain ⟨word,locals,tableNext,domain,installed,globals,memory⟩ := facts
    have atArrayNext : next.locals.lookup (ofString "arr") = some (.val (.word array)) := by
      rw [locals]
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
    exact decode_header_current_uint_suffix_bounded next array count input inputLength scratch frame ceiling inputLimit atArrayNext tableNext
      countBound above fits inputBound limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
      (installed.trans code) orderedFrame framePositive scratchBelow (by intro address lo hi; rw [domain]; exact arena address lo hi) remaining
  exact closed.weaken (by omega)

#print axioms source_decode_header_current_body
#print axioms decode_header_current_suffix_bounded
end InitECandidate.Runtime
