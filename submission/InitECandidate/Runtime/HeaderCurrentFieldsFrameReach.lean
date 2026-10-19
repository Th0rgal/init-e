import InitECandidate.Runtime.HeaderDecoderFieldsFrameReach
import InitECandidate.Runtime.HeaderWordFieldStepReach
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def headerCurrentWordContinuation : ProgHOL 64 := headerWordFieldStep 22 240 (decodeHeaderAt 57)
def headerCurrentUintContinuation : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "bg"),none)) (ofString "hdr_uint_field")
    [.var .local (ofString "arr"),.const 22,.const 8]) headerCurrentWordContinuation
def headerCurrentFieldContinuation : ProgHOL 64 := headerBytesStep 21 32 232 headerCurrentUintContinuation

theorem header_current_word_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (nonzero : flag ≠ 0)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s headerCurrentWordContinuation
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 57) := by
  have cb := g.currentCount nonzero
  have reached := header_word_field_step_reaches s array count input inputLength scratch frame record ceiling inputLimit 22 240 (decodeHeaderAt 57) (by decide)
    c.atArray c.atRecord g.before g.recordFits c.table (by simpa using (show 22 < count.toNat by omega)) g.above g.fits
    g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena
    (by unfold headerDecoderUnitCost at budget; omega)
  unfold headerCurrentWordContinuation
  apply reaches_mono s _ (decodeHeaderAt 57) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨word,locals,table,domain,installed,globals,memory⟩ := facts
  exact ⟨c.after_update (ofString "w") _ (by decide) locals table domain installed globals,domain,installed,globals,memory⟩

#print axioms header_current_word_frame_reaches

theorem header_current_bytes_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (nonzero : flag ≠ 0)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s headerCurrentFieldContinuation
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (headerCurrentUintContinuation) := by
  have cb := g.currentCount nonzero
  have reached := header_bytes_step_reaches s array count input inputLength scratch frame record ceiling inputLimit 21 32 232 (headerCurrentUintContinuation) (by decide)
    c.atArray c.atRecord g.before g.recordFits c.table (by simpa using (show 21 < count.toNat by omega)) g.above g.fits
    g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena
    (by unfold headerDecoderUnitCost at budget; omega)
  unfold headerCurrentFieldContinuation
  apply reaches_mono s _ (headerCurrentUintContinuation) _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨word,locals,table,domain,installed,globals,memory⟩ := facts
  exact ⟨c.after_update (ofString "f") _ (by decide) locals table domain installed globals,domain,installed,globals,memory⟩

#print axioms header_current_bytes_frame_reaches

theorem header_current_uint_call_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (nonzero : flag ≠ 0)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s headerCurrentUintContinuation
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) headerCurrentWordContinuation := by
  have cb := g.currentCount nonzero
  obtain ⟨pointer,length,entry⟩ := c.table (22#64) (by simpa using (show 22 < count.toNat by omega))
  have args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [.var .local (ofString "arr"),.const 22,.const 8] = some (headerRlpFieldValues .uint array 22 8) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,c.atArray,headerRlpFieldValues]
  have reached := header_rlp_field_assignment_reaches s .uint array 22 8 pointer length input inputLength scratch frame ceiling inputLimit
    (ofString "bg") [.var .local (ofString "arr"),.const 22,.const 8] headerCurrentWordContinuation args entry g.inputBound g.limitBound
    c.scratchGlobal c.frameGlobal c.code g.orderedFrame g.framePositive g.scratchBelow c.arena
    (by unfold headerDecoderUnitCost at budget; omega)
  unfold headerCurrentUintContinuation
  apply reaches_mono s _ headerCurrentWordContinuation _ _ _ _ (by unfold headerDecoderUnitCost; omega) ?_ reached
  intro post facts
  obtain ⟨value,locals,checked,domain,installed,globals,memory⟩ := facts
  have table := c.table.after_memory_from_ceiling s post array count input inputLength ceiling g.above g.fits domain memory
  exact ⟨c.after_update (ofString "bg") value (by decide) locals table domain installed globals,domain,installed,globals,
    fun address lo _ => memory address lo⟩

#print axioms header_current_uint_call_frame_reaches

theorem header_current_uint_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (nonzero : flag ≠ 0)
    (budget : 2 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s headerCurrentUintContinuation
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (2 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 57) := by
  have split : 2 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 1 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s headerCurrentUintContinuation headerCurrentWordContinuation (decodeHeaderAt 57) _ _ _ _ budget
    (header_current_uint_call_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c nonzero (by omega))
  intro next kept remaining
  apply reaches_mono next headerCurrentWordContinuation (decodeHeaderAt 57) _ _ _ _ (le_refl _) ?_
    (header_current_word_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context nonzero remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_current_uint_frame_reaches

theorem header_current_fields_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (nonzero : flag ≠ 0)
    (budget : 3 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s headerCurrentFieldContinuation
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (3 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 57) := by
  have split : 3 * headerDecoderUnitCost inputLimit =
      1 * headerDecoderUnitCost inputLimit + 2 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s headerCurrentFieldContinuation headerCurrentUintContinuation (decodeHeaderAt 57) _ _ _ _ budget
    (header_current_bytes_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c nonzero (by omega))
  intro next kept remaining
  apply reaches_mono next headerCurrentUintContinuation (decodeHeaderAt 57) _ _ _ _ (le_refl _) ?_
    (header_current_uint_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context nonzero remaining)
  intro post framed
  exact kept.trans framed

#print axioms header_current_fields_frame_reaches

end InitECandidate.Runtime
