import InitECandidate.Runtime.DecodeHeaderCurrentSuffixBound
import InitECandidate.Runtime.DecodeHeaderLegacySuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Both actual suffix branches and the final return satisfy one uniform
finite runtime bound; the legacy branch needs no additional slice entries. -/
theorem decode_header_final_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (flag : BitVec 64)
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (currentCount : flag ≠ 0 → 23 ≤ count.toNat)
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
    (budget : 3 * (headerRlpFieldCost inputLimit + 35) ≤ s.clock) : RunBounded s (decodeHeaderAt 56) (3 * (headerRlpFieldCost inputLimit + 35)) := by
  by_cases zero : flag = 0
  · exact (decode_header_legacy_suffix_bounded s code (by simpa [zero] using atFlag)).weaken (by omega)
  · have current := decode_header_current_suffix_bounded s array count input inputLength scratch frame record ceiling inputLimit
      (currentCount zero) atArray atRecord before recordFits table above fits inputBound limitBound scratchGlobal frameGlobal code
      orderedFrame framePositive scratchBelow arena budget
    have full : RunBounded s (.seq decodeHeaderCurrentSuffix (decodeHeaderAt 57))
        (3 * (headerRlpFieldCost inputLimit + 35)) := by
      apply RunBounded.seq (a := 3 * (headerRlpFieldCost inputLimit + 35)) (b := 0) current (by omega)
      intro next normal installed remaining
      rw [source_decode_header_return]
      exact RunBounded.ofProg (ProgBounded.straight _ rfl) (installed.trans code) (by omega)
    have nonzeroWord : flag ≠ (0#64) := zero
    have selected : evaluateHOLFiniteState s (.ite decodeHeaderCurrentCondition decodeHeaderCurrentSuffix decodeHeaderLegacySuffix) =
        evaluateHOLFiniteState s decodeHeaderCurrentSuffix := by
      simp [evaluateHOLFiniteState_ite,decodeHeaderCurrentCondition,evalHOLExact,atFlag,nonzeroWord,Compiler.Encoders.Asm.wordCmpHOL]
    unfold RunBounded at full ⊢
    rw [source_decode_header_current_suffix,evaluateHOLFiniteState_seq_line780,selected]
    rw [evaluateHOLFiniteState_seq_line780] at full
    exact full

#print axioms decode_header_final_suffix_bounded
end InitECandidate.Runtime
