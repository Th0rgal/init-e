import InitECandidate.Runtime.TransactionByteScopeBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionEmptyGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "len")) (.const 0)) (.raise (ofString "TxErr") (.const 1)) .skip

theorem source_transaction_body : sourceFunctionBody Guest.guestFn_decode_transaction_rlp =
    .seq transactionEmptyGuard (transactionAt 1) := by
  simp only [transactionEmptyGuard,transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_transaction_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (txBound : tx.toNat + 400 ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionAllocationSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_transaction_rlp)
    state.clock ≤ evaluated.2.clock + transactionAllocationSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "len")) (.const 0)) =
      some (.val (.word (if inputLength = (0 : BitVec 64) then (1 : BitVec 64) else 0))) := by
    by_cases zero : inputLength = 0 <;> simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,zero]
  rw [source_transaction_body,evaluateHOLFiniteState_seq_line780]
  unfold transactionEmptyGuard
  rw [evaluateHOLFiniteState_ite,condition]
  by_cases zero : inputLength = (0 : BitVec 64)
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
    have positive : 0 < inputLength.toNat := by
      have nonzero : inputLength.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      omega
    exact transaction_byte_scope_bounded state input inputLength scratch frame tx ceiling inputLimit pointerLocal lengthLocal positive noWrap inputBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena inputBeforeFrame inputBeforeArray reserve txAligned budget

#print axioms source_transaction_body
#print axioms evaluate_transaction_body_bounded
end InitECandidate.Runtime
