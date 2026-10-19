import InitECandidate.Runtime.DecodeHeaderBasefeeReach
import InitECandidate.Runtime.HeaderU256StoreContentFrame
/-!
The actual base-fee phase keeps the words it does not write.

`decode_header_basefee_reaches` only says that words below the record survive the
actual base-fee parser and its four-limb store.  The state root word at record offset
32 lies above the record, so carrying it to the returned header needs the
ceiling-based frame instead: the parser keeps every word at or above the workspace
ceiling, and the four-limb store keeps every such word other than its own four
destinations at offsets 160, 168, 176 and 184.  Both facts are actual, so the phase
below preserves any watched word at or above the ceiling that the store does not
overwrite.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual base-fee parser and four-limb record store keep every word at or
above the ceiling except the four destinations of the store. -/
theorem decode_header_basefee_content_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
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
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 160 →
          address ≠ record + BitVec.ofNat 64 160 + 8#64 →
          address ≠ record + BitVec.ofNat 64 160 + 16#64 →
          address ≠ record + BitVec.ofNat 64 160 + 24#64 →
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
  have store := header_u256_store_content_frame parsed array count input inputLength record first second third fourth 160
    (ofString "d") ceiling (decodeHeaderAt 44) (installed.trans code) atRecordParsed atValue (by decide) recordFits
    tableParsed before
  rw [source_decode_header_basefee_store]
  apply reaches_mono parsed _ (decodeHeaderAt 44) _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  refine ⟨first,second,third,fourth,localsReady.trans locals,tableReady,domainReady.trans domain,
    codeReady.trans installed,?_,?_⟩
  · intro global
    rw [globalsReady]
    exact globals global
  · intro address lo apart0 apart8 apart16 apart24
    exact (memoryReady address lo apart0 apart8 apart16 apart24).trans (memory address lo)

/-- The actual base-fee phase keeps a watched word at or above the ceiling that the
four-limb store does not overwrite, for instance the state root at record offset 32. -/
theorem decode_header_basefee_keeps_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record watched word : BitVec 64) (ceiling inputLimit : Nat)
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
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
    (watchedAbove : ceiling ≤ watched.toNat)
    (watched0 : watched ≠ record + BitVec.ofNat 64 160)
    (watched8 : watched ≠ record + BitVec.ofNat 64 160 + 8#64)
    (watched16 : watched ≠ record + BitVec.ofNat 64 160 + 16#64)
    (watched24 : watched ≠ record + BitVec.ofNat 64 160 + 24#64)
    (stored : s.memory watched = .word word) :
    Reaches s (decodeHeaderAt 42)
      (fun ready => ready.memory watched = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 160 →
          address ≠ record + BitVec.ofNat 64 160 + 8#64 →
          address ≠ record + BitVec.ofNat 64 160 + 16#64 →
          address ≠ record + BitVec.ofNat 64 160 + 24#64 →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  have frame := decode_header_basefee_content_frame s array count input inputLength scratch frame record ceiling
    inputLimit atArray atRecord before recordFits table countBound above fits inputBound limitBound scratchGlobal
    frameGlobal code orderedFrame framePositive scratchBelow arena budget
  refine reaches_mono s _ (decodeHeaderAt 44) _ _ _ _ (le_refl _) ?_ frame
  intro ready kept
  obtain ⟨first,second,third,fourth,_,_,domain,installed,globals,memory⟩ := kept
  exact ⟨(memory watched watchedAbove watched0 watched8 watched16 watched24).trans stored,domain,installed,globals,
    memory⟩

/-- The actual base-fee phase keeps the state root word at record offset 32, which
none of its four record destinations (offsets 160, 168, 176 and 184) overwrites. -/
theorem decode_header_basefee_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
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
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 42)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 160 →
          address ≠ record + BitVec.ofNat 64 160 + 8#64 →
          address ≠ record + BitVec.ofNat 64 160 + 16#64 →
          address ≠ record + BitVec.ofNat 64 160 + 24#64 →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  have targetNat : (BitVec.ofNat 64 32).toNat = 32 := Nat.mod_eq_of_lt (by decide)
  have rootSum : (record + BitVec.ofNat 64 32).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add,targetNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have hundredSixtyNat : (BitVec.ofNat 64 160).toNat = 160 := Nat.mod_eq_of_lt (by decide)
  have destinationSum : (record + BitVec.ofNat 64 160).toNat = record.toNat + 160 := by
    rw [BitVec.toNat_add,hundredSixtyNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have sourceSum (k : BitVec 64) (small : k.toNat ≤ 24) :
      ((record + BitVec.ofNat 64 160) + k).toNat = record.toNat + 160 + k.toNat := by
    rw [BitVec.toNat_add,destinationSum]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have apart (k : BitVec 64) (small : k.toNat ≤ 24) :
      record + BitVec.ofNat 64 32 ≠ (record + BitVec.ofNat 64 160) + k := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootSum,sourceSum k small] at both
    omega
  have zeroApart : record + BitVec.ofNat 64 32 ≠ record + BitVec.ofNat 64 160 := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootSum,destinationSum] at both
    omega
  have rootAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat := by
    rw [rootSum]
    omega
  exact decode_header_basefee_keeps_word s array count input inputLength scratch frame record
    (record + 32#64) word ceiling inputLimit atArray atRecord before recordFits table countBound above fits
    inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
    rootAbove zeroApart (apart (8#64) (by decide))
    (apart (16#64) (by decide)) (apart (24#64) (by decide))
    stored

#print axioms decode_header_basefee_keeps_state_root
#print axioms decode_header_basefee_content_frame
#print axioms decode_header_basefee_keeps_word
end InitECandidate.Runtime
