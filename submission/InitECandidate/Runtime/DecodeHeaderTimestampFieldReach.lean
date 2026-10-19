import InitECandidate.Runtime.DecodeHeaderInitialFieldsReach
import InitECandidate.Runtime.HeaderRlpFieldDeclarationReach
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem source_decode_header_timestamp_field : decodeHeaderAt 31 =
    .decCall (ofString "tsf") (.comb [.one,.one]) (ofString "hdr_uint_field")
      [.var .local (ofString "arr"),.const 11,.const 32] (decodeHeaderAt 32) := rfl

/-- The actual timestamp field call uses entry eleven of the real table, preserving
that entire table and the old header record above the parser workspace. -/
theorem decode_header_timestamp_field_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
      (headerRlpFieldCost inputLimit + 1) (decodeHeaderAt 32) := by
  obtain ⟨pointer,length,entry⟩ := table (11#64) (by simpa using (show 11 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const 11,.const 32] =
      some (headerRlpFieldValues .uint array 11 32) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerRlpFieldValues]
  have reached := header_rlp_field_declaration_reaches s .uint array 11 32 pointer length input inputLength scratch frame
    ceiling inputLimit (ofString "tsf") (.comb [.one,.one]) [.var .local (ofString "arr"),.const 11,.const 32] (decodeHeaderAt 32)
    args entry inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_decode_header_timestamp_field]
  apply reaches_mono s _ (decodeHeaderAt 32) _ _ (headerRlpFieldCost inputLimit + 1)
    (headerRlpFieldCost inputLimit + 1) (le_refl _) ?_ reached
  intro ready facts
  obtain ⟨value,locals,checked,_,domain,installed,globals,memory⟩ := facts
  exact ⟨value,locals,checked,table.after_memory_from_ceiling s ready array count input inputLength ceiling above fits domain memory,
    domain,installed,globals,memory⟩

#print axioms source_decode_header_timestamp_field
#print axioms decode_header_timestamp_field_reaches
end InitECandidate.Runtime
