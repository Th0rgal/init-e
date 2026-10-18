import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
import InitECandidate.Runtime.NormalLocalIncrementCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Nested decoder scopes restore every transaction local except the advanced index. -/
theorem transaction_access_extraction_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionAccessExtraction = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionAccessExtraction _ state post run
  simp [source_transaction_access_extraction,source_transaction_access_decode,transactionAccessFinish,
    normalLocalFrameSyntax,Ne.symm different]

theorem transaction_access_branch_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionAccessBranch _ state post run
  simp [source_transaction_access_branch,source_transaction_access_extraction,source_transaction_access_decode,
    transactionAccessFinish,normalLocalFrameSyntax,Ne.symm different]

/-- The extraction and decoder calls each consume their return and increment k once. -/
theorem transactionAccessExtraction_increments : NormalLocalIncrement (ofString "k") transactionAccessExtraction := by
  rw [source_transaction_access_extraction,source_transaction_access_decode]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  unfold transactionAccessFinish
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

/-- Normal branch completion skips legacy access lists and advances typed lists once. -/
theorem transaction_access_branch_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind index : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if kind = 0#64 then index else index + 1))) := by
  rw [source_transaction_access_branch,evaluateHOLFiniteState_ite] at run
  by_cases zero : kind = 0#64
  · subst kind
    have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0)) = some (.val (.word 0)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL]
    rw [condition] at run
    simp only [if_true,evaluateHOLFiniteState_skip] at run
    have same := (Prod.mk.inj run).2
    subst post
    simpa using indexLocal
  · have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,zero]
    rw [condition] at run
    simp only [show (1 : BitVec 64) ≠ 0 by decide,if_false] at run
    simpa only [zero,if_false] using transactionAccessExtraction_increments state post index indexLocal run

#print axioms transaction_access_extraction_other_local
#print axioms transaction_access_branch_other_local
#print axioms transactionAccessExtraction_increments
#print axioms transaction_access_branch_index
end InitECandidate.Runtime
