import InitECandidate.Runtime.DecodeHeaderFirstWordReach
import InitECandidate.Runtime.HeaderWordFieldStepContentFrame
import InitECandidate.Runtime.RecordOffsetAboveCeiling
/-!
The actual first-word phase at PC 25 keeps the state root word.

The frozen body runs `decodeHeaderAt 25` = `.decCall w .one hdr_word_field [arr,8]`
(`source_decode_header_first_word`) and then `decodeHeaderAt 26` =
`.seq (headerWordStore w 96)` (`source_decode_header_first_word_store`).  This module
composes exactly those two actual statements, not the standalone word-field step: the
declaration keeps every word at or above the ceiling, and the one-word store changes
only its own destination record + 96.  Hence the state root word at record offset 32 is
still there when the body reaches the next word parser at PC 27.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual first-word phase `decodeHeaderAt 25 -> decodeHeaderAt 27` keeps the
state root word at record offset 32 and every other word at or above the ceiling
outside record + 96. -/
theorem decode_header_first_word_keeps_state_root_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    Reaches s (decodeHeaderAt 25)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 96 → ready.memory address = s.memory address)
        ∧ ready.locals.lookup (ofString "is_current") = s.locals.lookup (ofString "is_current"))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) := by
  have rootAbove : ceiling ≤ (record + 32#64).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
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
  obtain ⟨pointer,length,entry⟩ := table (8#64) (by simpa using (show 8 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const 8] =
      some (headerNumericFieldValues .word array 8 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerNumericFieldValues]
  have firstCall := header_numeric_field_declaration_reaches s .word array 8 0 pointer length input inputLength scratch frame
    ceiling inputLimit (ofString "w") .one
    [.var .local (ofString "arr"),.const 8] (decodeHeaderAt 26) args entry inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  simp only [headerNumericFieldName] at firstCall
  rw [← source_decode_header_first_word] at firstCall
  apply reaches_trans s (decodeHeaderAt 25) (decodeHeaderAt 26) (decodeHeaderAt 27) _ _
    (headerRlpFieldCost inputLimit + 35) 0 firstCall
  intro parsed facts
  obtain ⟨value,locals,checked,_,domain,installed,globals,memory⟩ := facts
  have tableParsed : RlpSliceInputPrefix parsed array input inputLength count.toNat :=
    table.after_memory_from_ceiling s parsed array count input inputLength ceiling above fits domain memory
  obtain ⟨written,valueEq⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  subst value
  have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  have atValue : parsed.locals.lookup (ofString "w") =
      some (.val (.word written)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have store := header_word_store_content_frame parsed array count input inputLength record written 96 (ofString "w")
    (decodeHeaderAt 27) (installed.trans code) atRecordParsed atValue (by decide) recordFits tableParsed before
  rw [source_decode_header_first_word_store]
  apply reaches_mono parsed _ (decodeHeaderAt 27) _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨_,_,tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  have rootKept : ready.memory (record + 32#64) = .word word := by
    rw [memoryReady (record + 32#64) rootApart,memory (record + 32#64) rootAbove,stored]
  have atArrayParsed : parsed.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  have atArrayReady : ready.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [localsReady]
    exact atArrayParsed
  have atRecordReady : ready.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [localsReady]
    exact atRecordParsed
  refine ⟨rootKept,domainReady.trans domain,codeReady.trans installed,?_,tableReady,atArrayReady,atRecordReady,?_,?_⟩
  · intro global
    exact (congrArg (fun table => table.lookup global) globalsReady).trans (globals global)
  · intro address lo apart
    rw [memoryReady address apart,memory address lo]
  · rw [localsReady,locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms source_decode_header_first_word
#print axioms source_decode_header_first_word_store
#print axioms decode_header_first_word_keeps_state_root_locals
end InitECandidate.Runtime
