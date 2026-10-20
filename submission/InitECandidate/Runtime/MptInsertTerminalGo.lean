import InitECandidate.Runtime.MptInsertChoiceBound
import InitECandidate.Runtime.MptInsertNullStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A normal handler-free path which does not assign go retains its reset
value, including through real declaration calls and lexical scope restoration. -/
theorem mpt_insert_normal_go_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (program : ProgHOL 64) (supported : avoidsLocal (ofString "go") program=true)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s program=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
 have kept:=evaluate_avoidsLocal_flowing (ofString "go") program supported s
 rw [run] at kept
 exact (kept (Or.inl rfl)).trans zero

theorem mpt_insert_new_leaf_normal_stopped {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertNewLeafCall=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) :=
 mpt_insert_normal_go_frame s post _ (by decide) zero run

theorem mpt_insert_leaf_normal_stopped {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLeafDispatch=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
 apply mpt_insert_normal_go_frame s post _ _ zero run
 rw [source_mptInsert_leaf_dispatch]
 decide

theorem mpt_insert_split_normal_stopped {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertExtensionSplit=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
 apply mpt_insert_normal_go_frame s post _ _ zero run
 simp only [mptInsertExtensionSplit,mptInsertExtensionContinuation,mptInsertExtensionComparison,mptInsertKindDispatch,
  mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 decide

theorem mpt_insert_branch_value_normal_stopped {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertBranchValue=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
 apply mpt_insert_normal_go_frame s post _ _ zero run
 rw [source_mptInsert_branch_value]
 decide

/-- A normal extension comparison can continue the loop only by taking the
actual matched-prefix advance. The split constructor path leaves go zero. -/
theorem mpt_insert_extension_continuation_running {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (found segment : BitVec 64)
 (atPrefix : s.locals.lookup (ofString "pl")=some (.val (.word found)))
 (atSegment : s.locals.lookup (ofString "sl")=some (.val (.word segment)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertExtensionContinuation=(none,post)) :
 found=segment ∧evaluateHOLFiniteState s mptInsertExtensionAdvance=(none,post) := by
 rw [source_mptInsert_extension_continuation,evaluateHOLFiniteState_ite] at run
 by_cases matched : found=segment
 · have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl")))=some (.val (.word (1#64))) := by
    simp [evalHOLExact,atPrefix,atSegment,matched,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard] at run
   exact ⟨matched,run⟩
 · have guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.cmp .equal (.var .local (ofString "pl")) (.var .local (ofString "sl")))=some (.val (.word (0#64))) := by
    simp [evalHOLExact,atPrefix,atSegment,matched,Compiler.Encoders.Asm.wordCmpHOL]
   rw [guard] at run
   exact False.elim (running (mpt_insert_split_normal_stopped s post zero run))

#print axioms mpt_insert_new_leaf_normal_stopped
#print axioms mpt_insert_leaf_normal_stopped
#print axioms mpt_insert_split_normal_stopped
#print axioms mpt_insert_branch_value_normal_stopped
#print axioms mpt_insert_extension_continuation_running
end InitECandidate.Runtime
