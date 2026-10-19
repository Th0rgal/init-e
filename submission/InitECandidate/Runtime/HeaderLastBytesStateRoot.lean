import InitECandidate.Runtime.HeaderBytesChainContentFrame
import InitECandidate.Runtime.DecodeHeaderLastBytesReach
import InitECandidate.Runtime.RecordOffsetAboveCeiling
/-!
The actual last-bytes stretch keeps the state root word.

`decodeHeaderAt 52` is the real two-entry bytes-field chain for the encoded
uncle-hash list and the requests hash, stored at record offsets 216 and 224.
Neither writes offset 32, so the state root word is still there at PC 56.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual last bytes chain `decodeHeaderAt 38 -> 42` keeps the state root word
at record offset 32. -/
theorem decode_header_last_bytes_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (countBound : 21 ≤ count.toNat)
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
    (budget : decodeHeaderLastBytes.length * (headerRlpFieldCost inputLimit + 1) ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 52)
      (fun post => post.memory (record + 32#64) = .word word ∧
        HeaderBytesFrame s post array count input inputLength record ceiling)
      (decodeHeaderLastBytes.length * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 56) := by
  have valid : ∀ item ∈ decodeHeaderLastBytes, item.1.toNat < count.toNat ∧ item.2.2 < 248 := by
    intro item member
    simp only [decodeHeaderLastBytes,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · simp; omega
    · simp; omega
  have notWritten : ∀ item ∈ decodeHeaderLastBytes, item.2.2 ≠ 32 := by
    intro item member
    simp only [decodeHeaderLastBytes,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp
  have preservedAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have chain := header_bytes_chain_content_frame s array count input inputLength scratch frame record ceiling inputLimit
    decodeHeaderLastBytes (decodeHeaderAt 56) 32 word valid notWritten preservedAbove (by decide) stored
    atArray atRecord before recordFits table above fits inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena budget
  rwa [source_decode_header_last_bytes]

#print axioms decode_header_last_bytes_keeps_state_root
end InitECandidate.Runtime
