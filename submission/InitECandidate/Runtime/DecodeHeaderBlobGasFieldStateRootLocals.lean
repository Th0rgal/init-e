import InitECandidate.Runtime.DecodeHeaderBlobGasFieldReach
import InitECandidate.Runtime.RecordOffsetAboveCeiling
/-!
The actual blob-gas field call keeps the state root word.

`decodeHeaderAt 46` is the actual `hdr_uint_field` call for entry seventeen, bounded
by a shape check on the two-word pair.  It only touches memory below the workspace
ceiling, so the state root word at record offset 32 is still there at PC 47.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual blob-gas field call `decodeHeaderAt 46 -> 47` keeps the state root word
at record offset 32. -/
theorem decode_header_blobgas_field_keeps_state_root_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 18 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 46)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "h") = some (.val (.word record)) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address)
        ∧ ready.locals.lookup (ofString "is_current") = s.locals.lookup (ofString "is_current"))
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 47) := by
  have rootAbove : ceiling ≤ (record + 32#64).toNat :=
    record_offset_above_ceiling array count record ceiling 32 above before (by decide) recordFits
  have field := decode_header_blobgas_field_reaches s array count input inputLength scratch frame ceiling inputLimit
    atArray table countBound above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget
  refine reaches_mono s _ (decodeHeaderAt 47) _ _ (headerRlpFieldCost inputLimit + 1)
    (headerRlpFieldCost inputLimit + 1) (le_refl _) ?_ field
  intro ready facts
  obtain ⟨value,locals,shape,tableReady,domain,installed,globals,memory⟩ := facts
  have atArrayReady : ready.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  have atRecordReady : ready.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  refine And.intro ((memory (record + 32#64) rootAbove).trans stored) (And.intro domain
    (And.intro installed (And.intro globals (And.intro tableReady (And.intro atArrayReady
      (And.intro atRecordReady (And.intro memory ?_)))))))
  · rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms decode_header_blobgas_field_keeps_state_root_locals
end InitECandidate.Runtime
