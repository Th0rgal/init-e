import InitECandidate.Runtime.TransactionHeaderLowerFrame
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionRecordInitialization : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "tx"),.const 400])
    (.seq transactionInputPointerStore transactionInputLengthStore)

/-- Actual transaction record zeroing and input-header writes jointly preserve
all earlier words, including either header store's error path. -/
theorem transaction_record_initialization_lower_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx input length : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (budget : 401 ≤ state.clock)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address) :
    ∀ watched : BitVec 64, watched.toNat < tx.toNat →
      (evaluateHOLFiniteState state transactionRecordInitialization).2.memory watched = state.memory watched := by
  obtain ⟨middle,run,_,_,frame⟩ := evaluate_transaction_memzero_lower_frame state tx txLocal code budget small aligned arena
  have locals := evaluate_discard_call_success_locals state (ofString "memzero")
    [.var .local (ofString "tx"),.const 400] (by rw [run])
  rw [run] at locals
  intro watched before
  have headers := transaction_input_header_lower_frame middle tx input length
    (by rw [locals]; exact txLocal) (by rw [locals]; exact pointerLocal) (by rw [locals]; exact lengthLocal)
    (by omega) watched before
  rw [transactionRecordInitialization,evaluateHOLFiniteState_seq_line780,run]
  exact headers.trans (frame watched before)

/-- An older transaction-slice array remains readable and span-bounded across
initialization of a fresh transaction record. -/
theorem transaction_record_initialization_input_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx input length array count wholeInput wholeLength : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (budget : 401 ≤ state.clock)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (valid : RlpSliceInputPrefix state array wholeInput wholeLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat) :
    RlpSliceInputPrefix (evaluateHOLFiniteState state transactionRecordInitialization).2 array wholeInput wholeLength count.toNat := by
  exact rlp_slice_input_prefix_after_lower_frame state _ array count wholeInput wholeLength tx valid before
    (evaluateHOLFiniteState_metadata state transactionRecordInitialization).2.1
    (transaction_record_initialization_lower_frame state tx input length txLocal pointerLocal lengthLocal code budget small aligned arena)

#print axioms transaction_record_initialization_lower_frame
#print axioms transaction_record_initialization_input_prefix
end InitECandidate.Runtime
