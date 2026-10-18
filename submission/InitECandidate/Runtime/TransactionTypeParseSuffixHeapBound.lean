import InitECandidate.Runtime.TransactionTypeGuard
import InitECandidate.Runtime.TransactionLegacySuffixHeapBound
import InitECandidate.Runtime.TransactionTypedSuffixHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_parse_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame array tx kind : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (positive : 0 < inputLength.toNat) (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 9)
    state.clock ≤ evaluated.2.clock + transactionTypedSuffixCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have range := transaction_typed_decode_range input inputLength positive noWrap
  have costLe : transactionTypedSuffixCost (inputLength - 1).toNat inputLength.toNat ≤ transactionTypedSuffixCost inputLength.toNat inputLength.toNat := by
    have factor : (2 * (inputLength - 1).toNat + 1) * 15 + 19 ≤ (2 * inputLength.toNat + 1) * 15 + 19 := by omega
    have product := Nat.mul_le_mul range.2.2.2 factor
    unfold transactionTypedSuffixCost
    omega
  rw [source_transaction_type_parse,evaluateHOLFiniteState_seq_line780,source_transaction_type_branch,evaluateHOLFiniteState_ite,
    evaluate_transaction_byte_range state kind 1 4 byteLocal]
  by_cases typed : ¬ kind < (1 : BitVec 64) ∧ ¬ (4 : BitVec 64) < kind
  · rw [if_pos typed]
    dsimp only
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
    have bounded := transaction_typed_suffix_heap_bounded state input inputLength scratch frame array tx kind 0 ceiling inputLimit
      pointerLocal lengthLocal positive noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray txLocal typeLocal byteLocal countLocal
      (transaction_typed_guard_supported kind typed.1 typed.2) headerBefore arrayAbove (Nat.le_trans costLe budget)
    have enlarged : state.clock ≤ (evaluateHOLFiniteState state (.seq transactionTypedPath (transactionAt 10))).2.clock +
        transactionTypedSuffixCost inputLength.toNat inputLength.toNat ∧
        (evaluateHOLFiniteState state (.seq transactionTypedPath (transactionAt 10))).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state (.seq transactionTypedPath (transactionAt 10))).1 ≠ some .timeOut :=
      ⟨Nat.le_trans bounded.1 (Nat.add_le_add_left costLe _),bounded.2⟩
    simpa only [evaluateHOLFiniteState_seq_line780] using enlarged
  · rw [if_neg typed]
    dsimp only
    rw [if_pos (rfl : (0 : BitVec 64) = 0)]
    rw [evaluateHOLFiniteState_ite,evaluate_transaction_byte_range state kind 192 254 byteLocal]
    by_cases legacy : ¬ kind < (192 : BitVec 64) ∧ ¬ (254 : BitVec 64) < kind
    · rw [if_pos legacy]
      dsimp only
      rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
      have bounded := transaction_legacy_suffix_heap_bounded state input inputLength scratch frame array tx ceiling inputLimit
        pointerLocal lengthLocal noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray txLocal typeLocal countLocal headerBefore arrayAbove budget
      simpa only [evaluateHOLFiniteState_seq_line780] using bounded
    · rw [if_neg legacy]
      dsimp only
      rw [evaluateHOLFiniteState_raise]
      simp only [evalHOLExact]
      cases shape : state.eshapes.lookup (ofString "TxErr") with
      | none => simp
      | some shape =>
        dsimp only
        split_ifs <;> dsimp only <;> exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩

#print axioms transaction_type_parse_suffix_heap_bounded
end InitECandidate.Runtime
