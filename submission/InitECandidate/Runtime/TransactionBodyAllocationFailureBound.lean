import InitECandidate.Runtime.TransactionAllocationFailureBound
import InitECandidate.Runtime.TransactionBodyBound
import InitECandidate.Runtime.PanDecUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The byte load either rejects immediately or reaches the bounded failed
allocation; its declaration and local restoration consume no source ticks. -/
theorem transaction_byte_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 1)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  rw [source_transaction_byte_scope]
  apply evaluate_dec_one_uniform_bounded
  intro word
  exact transaction_allocation_failure_bounded (setVarHOLFinite (ofString "b0") (.val (.word word)) state) heap code heapGlobal request budget

/-- The complete decoder rejects an exhausted initial heap within two ticks,
including empty input and a failed initial byte load. -/
theorem transaction_body_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length heap : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "len")) (.const 0)) =
      some (.val (.word (if length = (0 : BitVec 64) then (1 : BitVec 64) else 0))) := by
    by_cases zero : length = 0 <;> simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,zero]
  rw [source_transaction_body,evaluateHOLFiniteState_seq_line780]
  unfold transactionEmptyGuard
  rw [evaluateHOLFiniteState_ite,condition]
  by_cases zero : length = (0 : BitVec 64)
  · rw [if_pos zero]
    dsimp only
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0),evaluateHOLFiniteState_raise]
    simp only [evalHOLExact]
    cases shape : state.eshapes.lookup (ofString "TxErr") with
    | none => simp
    | some shape =>
      dsimp only
      split_ifs <;> dsimp only <;> exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩
  · rw [if_neg zero]
    dsimp only
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_skip]
    have positive : 0 < length.toNat := by
      have nonzero : length.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    have bounded := transaction_byte_allocation_failure_bounded state heap code heapGlobal request budget
    exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩

#print axioms transaction_byte_allocation_failure_bounded
#print axioms transaction_body_allocation_failure_bounded
end InitECandidate.Runtime
