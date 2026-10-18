import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalAddCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The extraction and decoder calls each consume their return and increment k by two. -/
theorem transactionBlobExtraction_adds_two : NormalLocalAdd (ofString "k") 2 transactionBlobExtraction := by
  rw [source_transaction_blob_extraction,source_transaction_blob_decode]
  apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
  unfold transactionBlobFinish
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  exact normalLocalAdd_assign _ 2

theorem transactionBlobBody_adds_two : NormalLocalAdd (ofString "k") 2 transactionBlobBody := by
  rw [source_transaction_blob_body]
  apply normalLocalAdd_localCall _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  exact transactionBlobExtraction_adds_two

/-- The type-3 conditional advances the field index by two exactly when enabled. -/
theorem transaction_blob_branch_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind index : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionBlobBranch = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if kind = 3#64 then index + 2 else index))) := by
  rw [source_transaction_blob_branch,evaluateHOLFiniteState_ite] at run
  by_cases enabled : kind = 3#64
  · have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .equal (.var .local (ofString "t")) (.const 3)) = some (.val (.word 1)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,enabled]
    rw [condition] at run
    simp only [show (1 : BitVec 64) ≠ 0 by decide,if_false] at run
    simpa only [enabled,if_true] using transactionBlobBody_adds_two state post index indexLocal run
  · have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .equal (.var .local (ofString "t")) (.const 3)) = some (.val (.word 0)) := by
      simp [evalHOLExact,typeLocal,Compiler.Encoders.Asm.wordCmpHOL,enabled]
    rw [condition] at run
    simp only [if_true,evaluateHOLFiniteState_skip] at run
    have same := (Prod.mk.inj run).2
    subst post
    simpa only [enabled,if_false] using indexLocal


#print axioms transactionBlobExtraction_adds_two
#print axioms transactionBlobBody_adds_two
#print axioms transaction_blob_branch_index
end InitECandidate.Runtime
