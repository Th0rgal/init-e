import InitECandidate.Runtime.TransactionHeaderLowerFrame
import InitECandidate.Runtime.TransactionTypeStoreSuffixBound
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_top_guard_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 11) = (some (.returned value),post)) :
    evaluateHOLFiniteState state (transactionAt 12) = (some (.returned value),post) := by
  rw [source_transaction_top_guard,evaluateHOLFiniteState_seq_line780] at run
  unfold transactionTopGuard at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      exact run
    · have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 3)
      have noReturn := evaluate_raise_no_return state (ofString "TxErr") (.const 3) value
      cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 3)) with
      | mk result middle =>
        rw [raised] at run terminal noReturn
        cases result with
        | none => exact False.elim (terminal rfl)
        | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
  · cases run

/-- Returned field decoding passes the header store and list guard, retaining
all older slice entries and the environment needed for the allocating list call. -/
theorem transaction_type_header_returned_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx kind array count input inputLength : BitVec 64) (value : ValueHOL 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state (transactionAt 10) = (some (.returned value),post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 12) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧ middle.locals = state.locals ∧
      middle.globals = state.globals ∧ middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧ middle.clock = state.clock := by
  have noReturn := evaluate_noDirectReturn transactionTypeStore (by rfl) state value
  have frame := transaction_word_header_lower_frame state tx 0 kind (ofString "t") txLocal typeLocal
    (by change tx.toNat + 0 < 2^64; exact tx.isLt)
  change ∀ watched : BitVec 64, watched.toNat < tx.toNat →
    (evaluateHOLFiniteState state transactionTypeStore).2.memory watched = state.memory watched at frame
  have locals := (evaluate_store_control_frame state
    (.op .add [.var .local (ofString "tx"),.const 0]) (.var .local (ofString "t"))).2.1
  have globals : (evaluateHOLFiniteState state transactionTypeStore).2.globals = state.globals := by
    apply HolFiniteMapExact.ext
    funext name
    exact evaluate_avoidsGlobalAssignment name transactionTypeStore (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeStore
  have clock := clockPreserving_of_straightLine transactionTypeStore (by rfl) state
  rw [source_transaction_type_store,evaluateHOLFiniteState_seq_line780] at run
  cases stored : evaluateHOLFiniteState state transactionTypeStore with
  | mk result middle =>
    change (evaluateHOLFiniteState state transactionTypeStore).2.locals = state.locals at locals
    rw [stored] at run noReturn frame locals globals metadata clock
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      refine ⟨middle,transaction_top_guard_returned middle post value run,?_,locals,globals,metadata.1,metadata.2.1,clock⟩
      exact rlp_slice_input_prefix_after_lower_frame state middle array count input inputLength tx valid before metadata.2.1 frame

#print axioms transaction_top_guard_returned
#print axioms transaction_type_header_returned_input_prefix
end InitECandidate.Runtime
