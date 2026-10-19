import InitECandidate.Runtime.HeaderNumericFieldDeclarationReach
import InitECandidate.Runtime.HeaderWordStoreReach
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem source_decode_header_first_word : decodeHeaderAt 25 =
    .decCall (ofString "w") .one (ofString "hdr_word_field")
      [.var .local (ofString "arr"),.const 8] (decodeHeaderAt 26) := rfl

theorem source_decode_header_first_word_store : decodeHeaderAt 26 =
    .seq (headerWordStore (ofString "w") 96) (decodeHeaderAt 27) := rfl

/-- The actual first word parser and record store retain the whole
readable slice table and reach the next word parser within the numeric budget. -/
theorem decode_header_first_word_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 9 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock) :
    Reaches s (decodeHeaderAt 25)
      (fun ready => ∃ word : BitVec 64,
        ready.locals = s.locals.update (ofString "w",.val (.word word)) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < record.toNat →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 27) := by
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
  obtain ⟨word,valueEq⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  subst value
  have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  have atValue : parsed.locals.lookup (ofString "w") =
      some (.val (.word word)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have store := header_word_store_reaches parsed array count input inputLength record word 96 (ofString "w")
    (decodeHeaderAt 27) (installed.trans code) atRecordParsed atValue (by decide) recordFits tableParsed before
  rw [source_decode_header_first_word_store]
  apply reaches_mono parsed _ (decodeHeaderAt 27) _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  refine ⟨word,localsReady.trans locals,tableReady,domainReady.trans domain,codeReady.trans installed,?_,?_⟩
  · intro global
    rw [globalsReady]
    exact globals global
  · intro address lo hi
    exact (memoryReady address hi).trans (memory address lo)

#print axioms source_decode_header_first_word
#print axioms source_decode_header_first_word_store
#print axioms decode_header_first_word_reaches
end InitECandidate.Runtime
