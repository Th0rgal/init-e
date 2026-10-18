import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
import InitECandidate.Runtime.NormalLocalIncrementCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Nested decoder scopes restore every transaction local except the advanced index. -/
theorem transaction_authorization_extraction_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionAuthorizationExtraction = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionAuthorizationExtraction _ state post run
  simp [source_transaction_authorization_extraction,source_transaction_authorization_decode,transactionAuthorizationFinish,
    normalLocalFrameSyntax,Ne.symm different]

theorem transaction_authorization_branch_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionAuthorizationBranch _ state post run
  simp [source_transaction_authorization_branch,source_transaction_authorization_extraction,source_transaction_authorization_decode,
    transactionAuthorizationFinish,normalLocalFrameSyntax,Ne.symm different]

/-- The extraction and decoder calls each consume their return and increment k once. -/
theorem transactionAuthorizationExtraction_increments : NormalLocalIncrement (ofString "k") transactionAuthorizationExtraction := by
  rw [source_transaction_authorization_extraction,source_transaction_authorization_decode]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  unfold transactionAuthorizationFinish
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

/-- The type-4 conditional advances the field index once exactly when enabled. -/
theorem transaction_authorization_branch_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind index : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if kind = 4#64 then index + 1 else index))) := by
  rw [source_transaction_authorization_branch,evaluateHOLFiniteState_ite] at run
  by_cases enabled : kind = 4#64
  · have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .equal (.var .local (ofString "t")) (.const 4)) = some (.val (.word 1)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,enabled]
    rw [condition] at run
    simp only [show (1 : BitVec 64) ≠ 0 by decide,if_false] at run
    simpa only [enabled,if_true] using transactionAuthorizationExtraction_increments state post index indexLocal run
  · have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .equal (.var .local (ofString "t")) (.const 4)) = some (.val (.word 0)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,enabled]
    rw [condition] at run
    simp only [if_true,evaluateHOLFiniteState_skip] at run
    have same := (Prod.mk.inj run).2
    subst post
    simpa only [enabled,if_false] using indexLocal

#print axioms transaction_authorization_extraction_other_local
#print axioms transaction_authorization_branch_other_local
#print axioms transactionAuthorizationExtraction_increments
#print axioms transaction_authorization_branch_index
end InitECandidate.Runtime
