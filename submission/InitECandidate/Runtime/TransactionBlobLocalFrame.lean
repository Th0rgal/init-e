import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Blob-list extraction scopes retain every caller local except k. -/
theorem transaction_blob_extraction_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionBlobExtraction = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionBlobExtraction _ state post run
  simp [source_transaction_blob_extraction,source_transaction_blob_decode,transactionBlobFinish,
    normalLocalFrameSyntax,Ne.symm different]

/-- The complete blob branch retains caller locals other than its fee value and index. -/
theorem transaction_blob_branch_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notIndex : key ≠ ofString "k") (notValue : key ≠ ofString "v")
    (run : evaluateHOLFiniteState state transactionBlobBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionBlobBranch _ state post run
  simp [source_transaction_blob_branch,source_transaction_blob_body,source_transaction_blob_extraction,
    source_transaction_blob_decode,transactionBlobFinish,transactionBlobFeeStore,normalLocalFrameSyntax,
    Ne.symm notIndex,Ne.symm notValue]

#print axioms transaction_blob_extraction_other_local
#print axioms transaction_blob_branch_other_local
end InitECandidate.Runtime
