import InitECandidate.Runtime.DecodeHeaderTimestampFieldReach
import InitECandidate.Runtime.DecodeHeaderTimestampGuardReach
import InitECandidate.Runtime.RecordOffsetAboveCeiling
/-!
The actual timestamp-field stretch keeps the state root word.

The frozen body parses the timestamp field into local `tsf` (PC 31 to PC 32) and then
runs the width guard (PC 32 to PC 33).  Neither writes any record word: the parser only
touches memory below the ceiling and the guard either rejects or leaves the state
exactly as it was.  So the state root word at record offset 32 is still there when the
body reaches the timestamp word parser.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual timestamp field call and its width guard keep the state root word at
record offset 32. -/
theorem decode_header_timestamp_field_keeps_state_root {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 12 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 31)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 33) := by
  have rootAbove : ceiling ≤ (record + 32#64).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have field := decode_header_timestamp_field_reaches s array count input inputLength scratch frame ceiling inputLimit
    atArray table countBound above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget
  apply reaches_trans s (decodeHeaderAt 31) (decodeHeaderAt 32) (decodeHeaderAt 33) _ _
    (headerRlpFieldCost inputLimit + 1) 0 field
  intro parsed facts
  obtain ⟨value,locals,shape,tableParsed,domain,installed,globals,memory⟩ := facts
  have storedParsed : parsed.memory (record + 32#64) = .word word :=
    (memory (record + 32#64) rootAbove).trans stored
  have guard := decode_header_timestamp_guard_reaches parsed (installed.trans code)
  refine reaches_mono parsed _ (decodeHeaderAt 33) _ _ 0 0 (le_refl _) ?_ guard
  intro post kept
  subst kept
  have atArrayReady : post.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  have atRecordReady : post.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  exact ⟨storedParsed,domain,installed,globals,tableParsed,atArrayReady,atRecordReady,memory⟩

#print axioms decode_header_timestamp_field_keeps_state_root
end InitECandidate.Runtime
