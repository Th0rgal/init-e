import InitECandidate.Runtime.JournalSavedValuesAppend
import InitECandidate.Runtime.JournalRecordSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute jset's original saved-value stores and expose the enlarged undo
predicate at the exact continuation state. -/
theorem evaluate_journalRecordSource_saved_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal count table key present value : BitVec 64) (watched targets : Set (BitVec 64))
    (valid : JournalSavedValuesIn journal count.toNat watched targets state)
    (bounded : journal.toNat + (count.toNat + 1) * 32 ≤ 33806089496)
    (aligned : journal.toNat % 8 = 0)
    (registered : table ∈ watched → present ≠ 0 → value ∈ targets)
    (r : state.locals.lookup (ofString "r") = some (.val (.word (journal + count * 32))))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + count * 32 + BitVec.ofNat 64 offset)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      (∀ continuation, evaluateHOLFiniteState state (journalRecordSource32 continuation) = evaluateHOLFiniteState post continuation) ∧
      JournalSavedValuesIn journal (count.toNat + 1) watched targets post ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  exact ⟨journalRecordPost32 state (journal + count * 32) table key present value,
    (fun continuation => evaluate_journalRecordSource32 state (journal + count * 32) table key present value continuation r t kc old domain),
    valid.record_stores state journal count table key present value watched targets bounded aligned registered,
    rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_journalRecordSource_saved_values_in
end InitECandidate.Runtime
