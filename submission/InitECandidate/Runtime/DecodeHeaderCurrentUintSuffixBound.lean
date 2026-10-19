import InitECandidate.Runtime.DecodeHeaderCurrentSource
import InitECandidate.Runtime.HeaderNumericFieldCallBound
import InitECandidate.Runtime.HeaderRlpFieldCallFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def decodeHeaderCurrentWordSuffix : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "w"),none)) (ofString "hdr_word_field")
    [.var .local (ofString "arr"),.const 22]) (headerWordStore (ofString "w") 240)

def decodeHeaderCurrentUintSuffix : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "bg"),none)) (ofString "hdr_uint_field")
    [.var .local (ofString "arr"),.const 22,.const 8]) decodeHeaderCurrentWordSuffix

/-- The final current-header word call and store are bounded in every outcome. -/
theorem decode_header_current_word_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 23 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock) :
    RunBounded s decodeHeaderCurrentWordSuffix (headerRlpFieldCost inputLimit + 35) := by
  obtain ⟨pointer,length,entry⟩ := table (22#64) (by simpa using (show 22 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const 22] = some (headerNumericFieldValues .word array 22 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerNumericFieldValues]
  have callBound := runBounded_header_numeric_field_call s .word array 22 0 pointer length input inputLength scratch frame ceiling inputLimit
    (some (.local,ofString "w")) [.var .local (ofString "arr"),.const 22] args entry inputBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena budget
  unfold decodeHeaderCurrentWordSuffix
  apply RunBounded.seq (a := headerRlpFieldCost inputLimit + 35) (b := 0) callBound (by omega)
  intro next normal installed remaining
  exact RunBounded.ofProg (ProgBounded.straight _ rfl) (installed.trans code) (by omega)

theorem decode_header_current_uint_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 23 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : (headerRlpFieldCost inputLimit + 1) + (headerRlpFieldCost inputLimit + 35) ≤ s.clock) :
    RunBounded s decodeHeaderCurrentUintSuffix ((headerRlpFieldCost inputLimit + 1) + (headerRlpFieldCost inputLimit + 35)) := by
  obtain ⟨pointer,length,entry⟩ := table (22#64) (by simpa using (show 22 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const 22,.const 8] = some (headerRlpFieldValues .uint array 22 8) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerRlpFieldValues]
  have callBudget : headerRlpFieldCost inputLimit + 1 ≤ s.clock := by omega
  have callBound := runBounded_header_rlp_field_call s .uint array 22 8 pointer length input inputLength scratch frame ceiling inputLimit
    (some (.local,ofString "bg")) [.var .local (ofString "arr"),.const 22,.const 8] args entry inputBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena callBudget
  unfold decodeHeaderCurrentUintSuffix
  apply RunBounded.seq (a := headerRlpFieldCost inputLimit + 1) (b := headerRlpFieldCost inputLimit + 35) callBound budget
  intro next normal installed remaining
  obtain ⟨value,locals,checked,domain,_,globals,memory⟩ := header_rlp_field_call_normal_frame s next .uint array 22 8 pointer length input inputLength
    scratch frame ceiling inputLimit (ofString "bg") [.var .local (ofString "arr"),.const 22,.const 8]
    args entry inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena callBudget normal
  have atArrayNext : next.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  have tableNext := table.after_memory_from_ceiling s next array count input inputLength ceiling above fits domain memory
  exact decode_header_current_word_suffix_bounded next array count input inputLength scratch frame ceiling inputLimit atArrayNext tableNext
    countBound above fits inputBound limitBound (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (installed.trans code) orderedFrame framePositive scratchBelow (by intro address lo hi; rw [domain]; exact arena address lo hi) remaining

#print axioms decode_header_current_word_suffix_bounded
#print axioms decode_header_current_uint_suffix_bounded
end InitECandidate.Runtime
