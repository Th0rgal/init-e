import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.TransactionDecoderSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionPairFinish (name : MlS) (offset0 offset1 advance : BitVec 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "tx"),.const offset0]) (.rfield 0 (.var .local name)))
    (.seq (.store (.op .add [.var .local (ofString "tx"),.const offset1]) (.rfield 1 (.var .local name)))
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const advance])))

/-- Pair-valued decoder results are stored before the transaction's field slice array. -/
theorem transaction_pair_finish_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (tx first second offset0 offset1 advance array count input inputLength : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (resultLocal : state.locals.lookup name = some (.rStruct [.val (.word first),.val (.word second)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before0 : tx.toNat + offset0.toNat < array.toNat)
    (before1 : tx.toNat + offset1.toNat < array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (transactionPairFinish name offset0 offset1 advance)).2 array input inputLength count.toNat := by
  have nat0 : (tx + offset0).toNat = tx.toNat + offset0.toNat :=
    BitVec.toNat_add_of_lt (Nat.lt_trans before0 array.isLt)
  have nat1 : (tx + offset1).toNat = tx.toNat + offset1.toNat :=
    BitVec.toNat_add_of_lt (Nat.lt_trans before1 array.isLt)
  apply valid.after_memory_above state _ array count input inputLength fits
    (evaluateHOLFiniteState_metadata state (transactionPairFinish name offset0 offset1 advance)).2.1
  intro watched above
  have chain : BoundWordStoreChainFrame (F := F) state.locals watched (transactionPairFinish name offset0 offset1 advance) := by
    unfold transactionPairFinish
    apply BoundWordStoreChainFrame.store
    · intro current same
      refine ⟨tx + offset0,?_,?_⟩
      · simp [evalHOLExact,evalListHOLExact,same,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
      · intro equal; have same := congrArg BitVec.toNat equal; rw [nat0] at same; omega
    · intro current same parsed evaluated
      have actual : @evalHOLExact 64 F _ current.toExact (fun a => Classical.propDecidable (current.memaddrs a))
          (.rfield 0 (.var .local name)) = some (.val (.word first)) := by simp [evalHOLExact,same,resultLocal]
      rw [actual] at evaluated
      exact ⟨first,(Option.some.inj evaluated).symm⟩
    apply BoundWordStoreChainFrame.store
    · intro current same
      refine ⟨tx + offset1,?_,?_⟩
      · simp [evalHOLExact,evalListHOLExact,same,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
      · intro equal; have same := congrArg BitVec.toNat equal; rw [nat1] at same; omega
    · intro current same parsed evaluated
      have actual : @evalHOLExact 64 F _ current.toExact (fun a => Classical.propDecidable (current.memaddrs a))
          (.rfield 1 (.var .local name)) = some (.val (.word second)) := by simp [evalHOLExact,same,resultLocal]
      rw [actual] at evaluated
      exact ⟨second,(Option.some.inj evaluated).symm⟩
    exact BoundWordStoreChainFrame.tail _ (by rfl)
  exact evaluate_boundWordStoreChain_frame chain state rfl

theorem source_transaction_access_finish_pair : transactionAccessFinish =
    transactionPairFinish (ofString "acc") 208 216 1 := by rfl

theorem source_transaction_blob_finish_pair : transactionBlobFinish =
    transactionPairFinish (ofString "bh") 256 264 2 := by rfl

theorem source_transaction_authorization_finish_pair : transactionAuthorizationFinish =
    transactionPairFinish (ofString "au") 272 280 1 := by rfl

#print axioms transaction_pair_finish_input_prefix
end InitECandidate.Runtime
