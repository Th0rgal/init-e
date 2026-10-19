import InitECandidate.Runtime.DecodeHeaderTimestampGuardReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The actual timestamp parser and its width guard reach the following
word parser with the readable table and all workspace globals retained. -/
theorem decode_header_timestamp_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 12 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock) :
    Reaches s (decodeHeaderAt 31)
      (fun ready => ∃ value : ValueHOL 64,
        ready.locals = s.locals.update (ofString "tsf",value) ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 33) := by
  have first := decode_header_timestamp_field_reaches s array count input inputLength scratch frame ceiling inputLimit atArray table
    countBound above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  apply reaches_trans s (decodeHeaderAt 31) (decodeHeaderAt 32) (decodeHeaderAt 33) _ _
    (headerRlpFieldCost inputLimit + 1) 0 first
  intro parsed facts
  have retained := facts
  obtain ⟨value,locals,checked,tableParsed,domain,installed,globals,memory⟩ := facts
  apply reaches_mono parsed (decodeHeaderAt 32) (decodeHeaderAt 33) _ _ 0 0 (le_refl _) ?_
    (decode_header_timestamp_guard_reaches parsed (installed.trans code))
  intro post same
  subst post
  exact retained

#print axioms decode_header_timestamp_entry_reaches
end InitECandidate.Runtime
