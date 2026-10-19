import InitECandidate.Runtime.HeaderCurrentFieldsFrameReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem sequence_tail_congr {F : Type} (s : PanSemStateFiniteExact 64 F) (first second third : ProgHOL 64)
    (same : ∀ next : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState next second = evaluateHOLFiniteState next third) :
    evaluateHOLFiniteState s (.seq first second) = evaluateHOLFiniteState s (.seq first third) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  simp_rw [same]

private theorem reaches_same_evaluation {F : Type} (s : PanSemStateFiniteExact 64 F) (program normalized tail : ProgHOL 64)
    (P : PanSemStateFiniteExact 64 F → Prop) (cost : Nat)
    (same : evaluateHOLFiniteState s program = evaluateHOLFiniteState s normalized)
    (reached : Reaches s normalized P cost tail) : Reaches s program P cost tail := by
  unfold Reaches at reached ⊢
  rw [same]
  exact reached

theorem evaluate_header_current_suffix_normalized {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState s (.seq decodeHeaderCurrentSuffix (decodeHeaderAt 57)) =
      evaluateHOLFiniteState s headerCurrentFieldContinuation := by
  unfold decodeHeaderCurrentSuffix headerCurrentFieldContinuation headerBytesStep headerCurrentUintContinuation
    headerCurrentWordContinuation headerWordFieldStep
  rw [evaluate_seq_assoc]
  apply sequence_tail_congr
  intro next
  rw [evaluate_seq_assoc]
  apply sequence_tail_congr
  intro next2
  rw [evaluate_seq_assoc]
  apply sequence_tail_congr
  intro next3
  rw [evaluate_seq_assoc]

theorem header_legacy_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
 :
    Reaches s (.seq decodeHeaderLegacySuffix (decodeHeaderAt 57))
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      0 (decodeHeaderAt 57) := by
  have first := header_expression_store_reaches s array count input inputLength record 0 232 (.const 0)
    (.seq (headerExpressionStore (.const 0) 240) (decodeHeaderAt 57)) c.code c.atRecord
    (by simp [evalHOLExact]) (by decide) g.recordFits c.table g.before
  have combined : Reaches s (.seq (headerExpressionStore (.const 0) 232)
      (.seq (headerExpressionStore (.const 0) 240) (decodeHeaderAt 57)))
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      0 (decodeHeaderAt 57) := by
    apply reaches_trans s _ _ (decodeHeaderAt 57) _ _ 0 0 first
    intro parsed facts
    obtain ⟨table,locals,globals,domain,installed,memory⟩ := facts
    have ready := c.after_frame table (fun name _ => by rw [locals]) domain installed (fun name => by rw [globals])
    have second := header_expression_store_reaches parsed array count input inputLength record 0 240 (.const 0) (decodeHeaderAt 57)
      ready.code ready.atRecord (by simp [evalHOLExact]) (by decide) g.recordFits ready.table g.before
    apply reaches_mono parsed _ (decodeHeaderAt 57) _ _ 0 0 (le_refl _) ?_ second
    intro post facts
    obtain ⟨tablePost,localsPost,globalsPost,domainPost,codePost,memoryPost⟩ := facts
    refine ⟨ready.after_frame tablePost (fun name _ => by rw [localsPost]) domainPost codePost (fun name => by rw [globalsPost]),
      domainPost.trans domain,codePost.trans installed,?_,?_⟩
    · intro name
      rw [globalsPost,globals]
    · intro address lo hi
      exact (memoryPost address hi).trans (memory address hi)
  apply reaches_same_evaluation s _ _ (decodeHeaderAt 57) _ 0 ?_ combined
  unfold decodeHeaderLegacySuffix
  exact evaluate_seq_assoc s _ _ _

#print axioms evaluate_header_current_suffix_normalized
#print axioms header_legacy_frame_reaches

theorem header_final_frame_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling inputLimit : Nat)
    (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (budget : 3 * headerDecoderUnitCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 56)
      (fun post => HeaderDecoderFrame s post array count input inputLength scratch frame record flag ceiling)
      (3 * headerDecoderUnitCost inputLimit) (decodeHeaderAt 57) := by
  by_cases zero : flag = 0
  · have legacy := header_legacy_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c
    have selected : evaluateHOLFiniteState s (.ite decodeHeaderCurrentCondition decodeHeaderCurrentSuffix decodeHeaderLegacySuffix) =
        evaluateHOLFiniteState s decodeHeaderLegacySuffix := by
      simp [evaluateHOLFiniteState_ite,decodeHeaderCurrentCondition,evalHOLExact,c.atFlag,zero,Compiler.Encoders.Asm.wordCmpHOL]
    apply reaches_same_evaluation s (decodeHeaderAt 56) (.seq decodeHeaderLegacySuffix (decodeHeaderAt 57)) (decodeHeaderAt 57) _ _ ?_
      (reaches_mono s _ _ _ _ 0 _ (by omega) (fun _ h => h) legacy)
    rw [source_decode_header_current_suffix,evaluateHOLFiniteState_seq_line780,selected,← evaluateHOLFiniteState_seq_line780]
  · have current := header_current_fields_frame_reaches s array count input inputLength scratch frame record flag ceiling inputLimit g c zero budget
    have currentActual := reaches_same_evaluation s (.seq decodeHeaderCurrentSuffix (decodeHeaderAt 57))
      headerCurrentFieldContinuation (decodeHeaderAt 57) _ _ (evaluate_header_current_suffix_normalized s) current
    have nonzeroWord : flag ≠ (0#64) := zero
    have selected : evaluateHOLFiniteState s (.ite decodeHeaderCurrentCondition decodeHeaderCurrentSuffix decodeHeaderLegacySuffix) =
        evaluateHOLFiniteState s decodeHeaderCurrentSuffix := by
      simp [evaluateHOLFiniteState_ite,decodeHeaderCurrentCondition,evalHOLExact,c.atFlag,nonzeroWord,Compiler.Encoders.Asm.wordCmpHOL]
    apply reaches_same_evaluation s (decodeHeaderAt 56) (.seq decodeHeaderCurrentSuffix (decodeHeaderAt 57)) (decodeHeaderAt 57) _ _ ?_ currentActual
    rw [source_decode_header_current_suffix,evaluateHOLFiniteState_seq_line780,selected,← evaluateHOLFiniteState_seq_line780]

#print axioms header_final_frame_reaches
end InitECandidate.Runtime
