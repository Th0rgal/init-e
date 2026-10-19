import InitECandidate.Runtime.HeaderNumericFieldAssignmentReach
import InitECandidate.Runtime.HeaderU256StoreReach
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.FourWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem source_decode_header_basefee : decodeHeaderAt 42 =
    .seq (.call (some (some (.local,ofString "d"),none)) (ofString "hdr_u256_field")
      [.var .local (ofString "arr"),.const 15,.const 0]) (decodeHeaderAt 43) := rfl

theorem source_decode_header_basefee_store : decodeHeaderAt 43 =
    .seq (headerWordStore (ofString "d") 160) (decodeHeaderAt 44) := rfl

/-- The actual base-fee parser and four-limb record store retain the whole
readable slice table and reach the withdrawals-root parser within the numeric budget. -/
theorem decode_header_basefee_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 16 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock) :
    Reaches s (decodeHeaderAt 42)
      (fun ready => ∃ first second third fourth : BitVec 64,
        ready.locals = s.locals.update (ofString "d",.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < record.toNat →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  obtain ⟨pointer,length,entry⟩ := table (15#64) (by simpa using (show 15 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const 15,.const 0] =
      some (headerNumericFieldValues .u256 array 15 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerNumericFieldValues]
  have firstCall := header_numeric_field_assignment_reaches s .u256 array 15 0 pointer length input inputLength scratch frame
    ceiling inputLimit (ofString "d")
    [.var .local (ofString "arr"),.const 15,.const 0] (decodeHeaderAt 43) args entry inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  simp only [headerNumericFieldName] at firstCall
  rw [← source_decode_header_basefee] at firstCall
  apply reaches_trans s (decodeHeaderAt 42) (decodeHeaderAt 43) (decodeHeaderAt 44) _ _
    (headerRlpFieldCost inputLimit + 35) 0 firstCall
  intro parsed facts
  obtain ⟨value,locals,checked,domain,installed,globals,memory⟩ := facts
  have tableParsed : RlpSliceInputPrefix parsed array input inputLength count.toNat :=
    table.after_memory_from_ceiling s parsed array count input inputLength ceiling above fits domain memory
  obtain ⟨first,second,third,fourth,valueEq⟩ := value_four_words_of_checked_shape value checked
  subst value
  have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  have atValue : parsed.locals.lookup (ofString "d") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have store := header_u256_store_reaches parsed array count input inputLength record first second third fourth 160 (ofString "d")
    (decodeHeaderAt 44) (installed.trans code) atRecordParsed atValue (by decide) recordFits tableParsed before
  rw [source_decode_header_basefee_store]
  apply reaches_mono parsed _ (decodeHeaderAt 44) _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  refine ⟨first,second,third,fourth,localsReady.trans locals,tableReady,domainReady.trans domain,codeReady.trans installed,?_,?_⟩
  · intro global
    rw [globalsReady]
    exact globals global
  · intro address lo hi
    exact (memoryReady address hi).trans (memory address lo)

#print axioms source_decode_header_basefee
#print axioms source_decode_header_basefee_store
#print axioms decode_header_basefee_reaches
end InitECandidate.Runtime
