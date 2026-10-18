import InitECandidate.Runtime.TransactionTopGuardSuffixBound
import InitECandidate.Runtime.TransactionListSuffixHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_top_guard_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind expected tag total : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : transactionRequiredFields kind ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (wholeInputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (topLocal : state.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (budget : transactionListSuffixCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 11)
    state.clock ≤ evaluated.2.clock + transactionListSuffixCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "top"))) (.const 1)) =
      some (.val (.word (if tag = 1#64 then (0 : BitVec 64) else 1))) := by
    by_cases equal : tag = 1#64 <;>
      simp [evalHOLExact,topLocal,Compiler.Encoders.Asm.wordCmpHOL,equal]
  rw [source_transaction_top_guard,evaluateHOLFiniteState_seq_line780]
  unfold transactionTopGuard
  rw [evaluateHOLFiniteState_ite,condition]
  by_cases equal : tag = 1#64
  · rw [if_pos equal]
    dsimp only
    rw [evaluateHOLFiniteState_skip]
    exact transaction_list_suffix_heap_bounded state pointer length scratch frame array input inputLength tx kind expected tag total ceiling inputLimit
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      inputBeforeFrame inputBeforeArray starts ends txLocal typeLocal wholeInputBeforeArray expectedLocal fields inputBound headerBefore arrayAbove wholeInputBeforeFrame topLocal budget
  · rw [if_neg equal]
    dsimp only
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0),evaluateHOLFiniteState_raise]
    simp only [evalHOLExact]
    cases shape : state.eshapes.lookup (ofString "TxErr") with
    | none => simp
    | some shape =>
      dsimp only
      split_ifs <;> dsimp only <;> exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩

#print axioms source_transaction_top_guard
#print axioms transaction_top_guard_suffix_heap_bounded
end InitECandidate.Runtime
