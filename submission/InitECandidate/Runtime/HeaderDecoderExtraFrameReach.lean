import InitECandidate.Runtime.HeaderDecoderFragmentFrameReach
import InitECandidate.Runtime.DecodeHeaderExtraStoresReach
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem header_frame_extra_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 1 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 35)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (1 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 38) := by
  have cb := g.countBound
  have raw := decode_header_extra_field_reaches s array count input inputLength scratch frame ceiling inputLimit
    c.atArray c.table (by omega) g.above g.fits g.inputBound g.limitBound c.scratchGlobal c.frameGlobal c.code
    g.orderedFrame g.framePositive g.scratchBelow c.arena (by unfold headerDecoderUnitCost at budget; omega)
  have combined : Reaches s (decodeHeaderAt 35)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      ((headerRlpFieldCost inputLimit + 1) + 0) (decodeHeaderAt 38) := by
    apply reaches_trans s (decodeHeaderAt 35) (decodeHeaderAt 36) (decodeHeaderAt 38) _ _
      (headerRlpFieldCost inputLimit + 1) 0 raw
    intro parsed facts
    obtain ⟨value,locals,checked,table,domain,installed,globals,memory⟩ := facts
    obtain ⟨pointer,length,valueEq⟩ := value_two_words_of_checked_shape value checked
    subst value
    have ready := c.after_update (ofString "ex") _ (by decide) locals table domain installed globals
    have atExtra : parsed.locals.lookup (ofString "ex") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
      rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    have stores := decode_header_extra_stores_reaches parsed array count input inputLength record pointer length
      ready.code ready.atRecord atExtra g.recordFits ready.table g.before
    apply reaches_mono parsed (decodeHeaderAt 36) (decodeHeaderAt 38) _ _ 0 0 (le_refl _) ?_ stores
    intro post facts
    obtain ⟨tablePost,localsPost,globalsPost,domainPost,codePost,memoryPost⟩ := facts
    refine ⟨ready.after_frame tablePost (fun name _ => by rw [localsPost]) domainPost codePost (fun name => by rw [globalsPost]),
      domainPost.trans domain,codePost.trans installed,?_,?_⟩
    · intro name
      rw [globalsPost]
      exact globals name
    · intro address lo hi
      exact (memoryPost address hi).trans (memory address lo)
  exact reaches_mono s (decodeHeaderAt 35) (decodeHeaderAt 38) _ _ _ _
    (by unfold headerDecoderUnitCost; omega) (fun _ h => h) combined

#print axioms header_frame_extra_reaches
end InitECandidate.Runtime
