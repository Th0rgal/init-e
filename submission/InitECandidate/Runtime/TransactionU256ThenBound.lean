import InitECandidate.Runtime.TransactionU256Witness
import InitECandidate.Runtime.TransactionU256FieldBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scalar field cost composes with any continuation proved from its concrete next witness. -/
theorem transaction_u256_then_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (offset maximum : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word valid.index),.val (.word maximum)])
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + offset.toNat + 24 < array.toNat)
    (tail : ProgHOL 64) (tailCost : Nat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + tailCost ≤ state.clock)
    (tailBound : ∀ post : PanSemStateFiniteExact 64 F, ∀ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index → next.heap = valid.heap → tailCost ≤ post.clock →
      let evaluated := evaluateHOLFiniteState post tail
      post.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ post.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.seq (transactionU256Field offset arguments) tail)
    state.clock ≤ evaluated.2.clock + ((inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have firstBudget : first ≤ state.clock := by omega
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const offset]) arguments array valid.index maximum input inputLength scratch frame count.toNat ceiling inputLimit
    args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state (transactionU256Field offset arguments)).2.clock + first ∧
    (evaluateHOLFiniteState state (transactionU256Field offset arguments)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (transactionU256Field offset arguments)).1 ≠ some .timeOut at bounded
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (transactionU256Field offset arguments) with
  | mk result post =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some stopped =>
      dsimp only
      exact ⟨by dsimp [first] at bounded; omega,bounded.2.1,bounded.2.2⟩
    | none =>
      dsimp only
      obtain ⟨next,indexEqual,heapEqual⟩ := transaction_decode_witness_after_u256 state post array count tx kind input inputLength scratch frame ceiling inputLimit
        valid offset maximum arguments args inside inputBound limitBound orderedFrame framePositive scratchBelow arrayBelow headerBefore firstBudget run
      have remaining := tailBound post next indexEqual heapEqual (by have spent := bounded.1; dsimp [first] at spent; omega)
      dsimp only at remaining
      exact ⟨by dsimp [first] at bounded; omega,Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_u256_then_bounded
end InitECandidate.Runtime
