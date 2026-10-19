import InitECandidate.Runtime.DecodeHeaderExtraFieldReach
import InitECandidate.Runtime.DecodeHeaderExtraStoresReach
import InitECandidate.Runtime.HeaderExpressionStoreFrame
import InitECandidate.Runtime.RecordOffsetAboveCeiling
/-!
The actual extra-data stretch keeps the state root word.

The frozen body parses the extra-data field into the pair local `ex` (PC 35 to PC 36) and
then stores its pointer and length at record offsets 128 and 136 (PC 36 to PC 38).  The
parse keeps every word at or above the workspace ceiling and each store changes only its
own destination, so the state root word at record offset 32 is still there at PC 38.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual extra-data stretch `decodeHeaderAt 35 -> 38` keeps the state root word at
record offset 32. -/
theorem decode_header_extra_field_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 13 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 35)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global))
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 38) := by
  have rootAbove : ceiling ≤ (record + 32#64).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have small32 : (32#64).toNat = 32 := by decide
  have small128 : (128#64).toNat = 128 := by decide
  have small136 : (136#64).toNat = 136 := by decide
  have rootNat : (record + BitVec.ofNat 64 32).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add,small32]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have rootApart128 : record + BitVec.ofNat 64 32 ≠ record + BitVec.ofNat 64 128 := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootNat] at both
    have destination : (record + BitVec.ofNat 64 128).toNat = record.toNat + 128 := by
      rw [BitVec.toNat_add,small128]
      exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
    rw [destination] at both
    omega
  have rootApart136 : record + BitVec.ofNat 64 32 ≠ record + BitVec.ofNat 64 136 := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootNat] at both
    have destination : (record + BitVec.ofNat 64 136).toNat = record.toNat + 136 := by
      rw [BitVec.toNat_add,small136]
      exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
    rw [destination] at both
    omega
  have field := decode_header_extra_field_reaches s array count input inputLength scratch frame ceiling inputLimit
    atArray table countBound above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget
  apply reaches_trans s (decodeHeaderAt 35) (decodeHeaderAt 36) (decodeHeaderAt 38) _ _
    (headerRlpFieldCost inputLimit + 1) 0 field
  intro parsed facts
  obtain ⟨value,locals,shape,tableParsed,domain,installed,globals,memory⟩ := facts
  obtain ⟨pointer,length,valueEq⟩ := value_two_words_of_checked_shape value shape
  subst value
  have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  have atExtra : parsed.locals.lookup (ofString "ex") =
      some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have rootKept : parsed.memory (record + 32#64) = .word word :=
    (memory (record + 32#64) rootAbove).trans stored
  have first := header_expression_store_frame parsed record pointer 128
    (.rfield 0 (.var .local (ofString "ex"))) (decodeHeaderAt 37) (installed.trans code) atRecordParsed
    (by simp [evalHOLExact,atExtra])
  apply reaches_trans parsed (decodeHeaderAt 36) (decodeHeaderAt 37) (decodeHeaderAt 38) _ _ 0 0 first
  intro storedReady storedFacts
  obtain ⟨localsStored,domainStored,codeStored,globalsStored,memoryStored⟩ := storedFacts
  have atRecordStored : storedReady.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [localsStored]; exact atRecordParsed
  have atExtraStored : storedReady.locals.lookup (ofString "ex") =
      some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    rw [localsStored]; exact atExtra
  have second := header_expression_store_frame storedReady record length 136
    (.rfield 1 (.var .local (ofString "ex"))) (decodeHeaderAt 38) (codeStored.trans (installed.trans code))
    atRecordStored (by simp [evalHOLExact,atExtraStored])
  apply reaches_mono storedReady _ (decodeHeaderAt 38) _ _ 0 0 (le_refl _) ?_ second
  intro post kept
  obtain ⟨localsPost,domainPost,codePost,globalsPost,memoryPost⟩ := kept
  refine ⟨?_,?_,?_,?_⟩
  · rw [memoryPost (record + 32#64) rootApart136,
        memoryStored (record + 32#64) rootApart128]
    exact rootKept
  · rw [domainPost,domainStored,domain]
  · rw [codePost,codeStored,installed,code]
  · intro global
    rw [globalsPost global,globalsStored global]
    exact globals global

#print axioms decode_header_extra_field_keeps_state_root
end InitECandidate.Runtime
