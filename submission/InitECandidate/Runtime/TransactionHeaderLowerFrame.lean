import InitECandidate.Runtime.TransactionMemzeroLowerFrame
import InitECandidate.Runtime.TransactionWordHeaderPrefix
import InitECandidate.Runtime.TransactionInputPointerStoreSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A scalar transaction-header store cannot alter words below the transaction
allocation, including when the store's domain check fails. -/
theorem transaction_word_header_lower_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx offset word : BitVec 64) (name : MlS)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valueLocal : state.locals.lookup name = some (.val (.word word)))
    (fits : tx.toNat + offset.toNat < 2^64) :
    ∀ watched : BitVec 64, watched.toNat < tx.toNat →
      (evaluateHOLFiniteState state (.store (.op .add [.var .local (ofString "tx"),.const offset])
        (.var .local name))).2.memory watched = state.memory watched := by
  intro watched before
  have addressNat : (tx + offset).toNat = tx.toNat + offset.toNat := BitVec.toNat_add_of_lt fits
  apply evaluate_wordStore_memory_frame state _ _ (tx + offset) watched
  · simp [evalHOLExact,evalListHOLExact,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro parsed evaluated
    have actual : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.var .local name) = some (.val (.word word)) := by simp [evalHOLExact,valueLocal]
    rw [actual] at evaluated
    exact ⟨word,(Option.some.inj evaluated).symm⟩
  · intro equal
    have nat := congrArg BitVec.toNat equal
    rw [addressNat] at nat
    omega

/-- Both original stores recording the input pointer and length preserve all
older allocation words, including either store's immediate error path. -/
theorem transaction_input_header_lower_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx input length : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (fits : tx.toNat + 400 ≤ 2^64) :
    ∀ watched : BitVec 64, watched.toNat < tx.toNat →
      (evaluateHOLFiniteState state (.seq transactionInputPointerStore transactionInputLengthStore)).2.memory watched = state.memory watched := by
  intro watched before
  have first := transaction_word_header_lower_frame state tx 384 input (ofString "p") txLocal pointerLocal
    (by change tx.toNat + 384 < 2^64; omega) watched before
  change (evaluateHOLFiniteState state transactionInputPointerStore).2.memory watched = _ at first
  have locals := (evaluate_store_control_frame state
    (.op .add [.var .local (ofString "tx"),.const 384]) (.var .local (ofString "p"))).2.1
  rw [evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state transactionInputPointerStore with
  | mk result middle =>
    rw [stored] at first
    change (evaluateHOLFiniteState state transactionInputPointerStore).2.locals = state.locals at locals
    rw [stored] at locals
    cases result with
    | some result => exact first
    | none =>
      dsimp only
      have second := transaction_word_header_lower_frame middle tx 392 length (ofString "len")
        (by rw [locals]; exact txLocal) (by rw [locals]; exact lengthLocal)
        (by change tx.toNat + 392 < 2^64; omega) watched before
      exact second.trans first

#print axioms transaction_word_header_lower_frame
#print axioms transaction_input_header_lower_frame
end InitECandidate.Runtime
