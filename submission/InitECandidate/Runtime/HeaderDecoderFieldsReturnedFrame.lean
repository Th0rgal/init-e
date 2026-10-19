import InitECandidate.Runtime.HeaderFinalFrameReach
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem header_fields_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 27 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 9)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (27 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 57) := by
  have split : 27 * headerDecoderUnitCost inputLimit = 24 * headerDecoderUnitCost inputLimit + 3 * headerDecoderUnitCost inputLimit := by omega
  rw [split] at budget ⊢
  apply reaches_trans_budget s (decodeHeaderAt 9) (decodeHeaderAt 56) (decodeHeaderAt 57) _ _ _ _ budget
    (header_fields_at9_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c (by omega))
  intro next kept remaining
  apply reaches_mono next (decodeHeaderAt 56) (decodeHeaderAt 57) _ _ _ _ (le_refl _) ?_
    (header_final_frame_reaches next array count input inputLength scratch frame record flag ceiling inputLimit g kept.context remaining)
  intro post framed
  exact kept.trans framed

/-- A returned execution of all actual header fields returns its allocated
record and preserves every global and every old heap word below that record. -/
theorem header_fields_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 27 * headerDecoderUnitCost inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeHeaderAt 9) = (some (.returned value),post)) :
    value = .val (.word record) ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ name : MlS, post.globals.lookup name = s.globals.lookup name) ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < record.toNat → post.memory address = s.memory address) := by
  have reached := header_fields_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c budget
  obtain ⟨ready,kept,_,_,agreement,returnedTail⟩ := reaches_returned_continuation s (decodeHeaderAt 9) (decodeHeaderAt 57) _
    (27 * headerDecoderUnitCost inputLimit) value reached (by rw [run])
  have tailMemory : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.memory = ready.memory := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have tailGlobals : (evaluateHOLFiniteState ready (decodeHeaderAt 57)).2.globals = ready.globals := by
    rw [source_decode_header_return,evaluateHOLFiniteState_return]
    repeat first | split | rfl
  have sourceMemory := agreement.2.2.1
  have sourceGlobals := agreement.2.2.2.1
  rw [run] at sourceMemory sourceGlobals
  have metadata := evaluateHOLFiniteState_metadata s (decodeHeaderAt 9)
  rw [run] at metadata
  refine ⟨?_,metadata.2.1,metadata.1,?_,?_⟩
  · rw [source_decode_header_return,evaluateHOLFiniteState_return] at returnedTail
    simpa [evalHOLExact,kept.context.atRecord,shapeOfHOLExact] using returnedTail.symm
  · intro name
    rw [sourceGlobals,tailGlobals]
    exact kept.globals name
  · intro address lo hi
    exact (congrFun (sourceMemory.trans tailMemory) address).trans (kept.memory address lo hi)

#print axioms header_fields_frame_reaches
#print axioms header_fields_returned_frame
end InitECandidate.Runtime
