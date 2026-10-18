import InitECandidate.Runtime.TransactionIndexAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Advance the actual field index before a continuation, retaining exact natural progress. -/
theorem transaction_index_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat) (continuation : ProgHOL 64) (cost : Nat)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index.toNat = valid.index.toNat + 1 → next.heap = valid.heap → middle.clock = state.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionIndexAdvance continuation)
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let next := valid.advanceIndex inside
  have nextNat : next.index.toNat = valid.index.toNat + 1 := by
    change (valid.index + 1).toNat = _
    rw [BitVec.toNat_add_of_lt (by have h := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have bounded := tailBound _ next nextNat rfl rfl
  rw [evaluateHOLFiniteState_seq_line780,transaction_index_advance_run state valid.index valid.indexLocal]
  exact bounded

#print axioms transaction_index_heap_continuation_bounded
end InitECandidate.Runtime
