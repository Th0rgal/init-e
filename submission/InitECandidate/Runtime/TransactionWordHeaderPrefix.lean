import InitECandidate.Runtime.TransactionPairHeaderPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_word_header_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx offset array count input inputLength word : BitVec 64) (name : MlS)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valueLocal : state.locals.lookup name = some (.val (.word word)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : tx.toNat + offset.toNat < array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state
      (.store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local name))).2 array input inputLength count.toNat := by
  let program : ProgHOL 64 := .store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local name)
  have addressNat : (tx + offset).toNat = tx.toNat + offset.toNat :=
    BitVec.toNat_add_of_lt (Nat.lt_trans before array.isLt)
  apply valid.after_memory_above state _ array count input inputLength fits (evaluateHOLFiniteState_metadata state program).2.1
  intro watched above
  apply evaluate_wordStore_memory_frame state _ _ (tx + offset) watched
  · simp [evalHOLExact,evalListHOLExact,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro parsed evaluated
    have actual : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.var .local name) = some (.val (.word word)) := by simp [evalHOLExact,valueLocal]
    rw [actual] at evaluated
    exact ⟨word,(Option.some.inj evaluated).symm⟩
  · intro equal; have nat := congrArg BitVec.toNat equal; rw [addressNat] at nat; omega

#print axioms transaction_word_header_prefix
end InitECandidate.Runtime
