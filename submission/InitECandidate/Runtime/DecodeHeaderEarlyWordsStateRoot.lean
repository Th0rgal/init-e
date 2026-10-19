import InitECandidate.Runtime.HeaderWordFieldChainContentFrame
import InitECandidate.Runtime.RecordOffsetAboveCeiling
import InitECandidate.Runtime.DecodeHeaderEarlyWordsReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual early-words span keeps the state root word at record offset 32. -/
theorem decode_header_early_words_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (countBound : 11 ≤ count.toNat)
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
    (budget : 2 * (headerRlpFieldCost inputLimit + 35) ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 27)
      (fun post => post.memory (record + 32#64) = .word word ∧
        HeaderWordFieldFrame s post array count input inputLength record ceiling)
      (2 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 31) := by
  have validSteps : ∀ item ∈ decodeHeaderEarlyWords, item.1.toNat < count.toNat ∧ item.2 < 248 := by
    intro item member
    obtain ⟨index,offset⟩ := item
    have facts : index.toNat ≤ 10 ∧ offset < 248 := by
      simp only [decodeHeaderEarlyWords,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
    exact ⟨Nat.lt_of_le_of_lt facts.1 (Nat.lt_of_lt_of_le (by decide : 10 < 11) countBound),facts.2⟩
  have notWritten : ∀ item ∈ decodeHeaderEarlyWords, item.2 ≠ 32 := by
    intro item member
    obtain ⟨index,offset⟩ := item
    simp only [decodeHeaderEarlyWords,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  have preservedAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have chain := header_word_field_chain_content_frame s array count input inputLength scratch frame record ceiling
    inputLimit decodeHeaderEarlyWords (decodeHeaderAt 31) 32 word validSteps notWritten preservedAbove (by decide)
    stored atArray atRecord before recordFits table above fits inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena budget
  rw [source_decode_header_early_words]
  exact chain

#print axioms decode_header_early_words_keeps_state_root
end InitECandidate.Runtime
