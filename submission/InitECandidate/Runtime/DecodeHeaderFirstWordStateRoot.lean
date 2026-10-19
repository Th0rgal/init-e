import InitECandidate.Runtime.HeaderWordFieldStepContentFrame
import InitECandidate.Runtime.RecordOffsetAboveCeiling
import InitECandidate.Runtime.DecodeHeaderFirstWordReach
/-!
The actual first-word phase keeps the state root word.

The real body parses the first word at slice offset 8 and stores it at record offset
96 (`source_decode_header_first_word` followed by
`source_decode_header_first_word_store`, both rfl against the frozen body).  That
single actual word-field step writes only its own destination, so the state root word
at record offset 32 is still there when the step reaches the next word parser.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual first-word step keeps the state root word at record offset 32. -/
theorem decode_header_first_word_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (countBound : 9 ≤ count.toNat)
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
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (headerWordFieldStep 8#64 96 (decodeHeaderAt 27))
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 96 → ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) := by
  have small32 : (32#64).toNat = 32 := by decide
  have small96 : (96#64).toNat = 96 := by decide
  have rootNat : (record + BitVec.ofNat 64 32).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add,small32]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have destinationNat : (record + BitVec.ofNat 64 96).toNat = record.toNat + 96 := by
    rw [BitVec.toNat_add,small96]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have rootApart : record + BitVec.ofNat 64 32 ≠ record + BitVec.ofNat 64 96 := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootNat,destinationNat] at both
    omega
  have rootAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have step := header_word_field_step_content_frame s array count input inputLength scratch frame record ceiling
    inputLimit 8#64 96 (decodeHeaderAt 27) (by decide) atArray atRecord before recordFits table
    (by simpa using (show 8 < count.toNat by omega)) above fits inputBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena budget
  refine reaches_mono s _ (decodeHeaderAt 27) _ _ _ _ (le_refl _) ?_ step
  intro ready kept
  obtain ⟨parsedWord,_,_,_,_,domain,installed,globals,memory⟩ := kept
  refine ⟨?_,domain,installed,globals,memory⟩
  exact (memory (record + 32#64) rootAbove rootApart).trans stored

#print axioms decode_header_first_word_keeps_state_root
end InitECandidate.Runtime
