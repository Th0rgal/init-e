import InitECandidate.Runtime.TransactionPairHeaderPrefix
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_pair_finish_outer_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (tx first second offset0 offset1 advance array count input inputLength : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (resultLocal : state.locals.lookup name = some (.rStruct [.val (.word first),.val (.word second)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (fits0 : tx.toNat + offset0.toNat < 2^64)
    (fits1 : tx.toNat + offset1.toNat < 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state (transactionPairFinish name offset0 offset1 advance)).2 array input inputLength count.toNat := by
  have nat0 : (tx + offset0).toNat = tx.toNat + offset0.toNat :=
    BitVec.toNat_add_of_lt fits0
  have nat1 : (tx + offset1).toNat = tx.toNat + offset1.toNat :=
    BitVec.toNat_add_of_lt fits1
  apply valid.after_memory_below state _ array count input inputLength tx before
    (evaluateHOLFiniteState_metadata state (transactionPairFinish name offset0 offset1 advance)).2.1
  intro watched below
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

#print axioms transaction_pair_finish_outer_prefix
end InitECandidate.Runtime
