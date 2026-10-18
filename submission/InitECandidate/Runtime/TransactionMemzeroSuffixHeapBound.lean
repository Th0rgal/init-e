import InitECandidate.Runtime.TransactionMemzeroSuffixBound
import InitECandidate.Runtime.TransactionInputPointerStoreSuffixHeapBound
import InitECandidate.Runtime.MemzeroAlignedCall
import InitECandidate.Runtime.MemzeroIntervalDomains
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_memzero_suffix_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (txSmall : tx.toNat + 400 ≤ 33806089496)
    (txAligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (budget : transactionMemzeroSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 3)
    state.clock ≤ evaluated.2.clock + transactionMemzeroSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨wordDomain,byteDomain⟩ := memzero_interval_domains state tx 400 txAligned (by change tx.toNat + 400 ≤ 2^64; omega) txArena
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "tx"),.const 400] = some [.val (.word tx),.val (.word (400 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,txLocal]
  have ticks : 401 + transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ state.clock := budget
  obtain ⟨post,run,zeroed,spent,remaining,globals,postCode,domain,endian,locals,occupancy⟩ :=
    evaluate_memzero_aligned_call state (.var .local (ofString "tx")) (.const 400) tx 400 args code
      (by change 401 ≤ state.clock; omega) txSmall txAligned wordDomain byteDomain
  have futureBudget : transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ post.clock := by
    change state.clock ≤ post.clock + 400 + 1 at spent
    omega
  have bounded := transaction_input_pointer_store_suffix_heap_bounded post input inputLength scratch frame array tx kind ceiling inputLimit
    (by rw [locals]; exact pointerLocal) (by rw [locals]; exact lengthLocal) positive noWrap inputBound limitBound
    (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal) (postCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; rw [domain]; exact arena address low high)
    (by rw [globals]; exact heap) arrayBound countLimit
    (by intro address low high; rw [domain]; exact heapArena address low high)
    inputBeforeFrame inputBeforeArray (by rw [locals]; exact txLocal) (by rw [locals]; exact byteLocal) headerBefore arrayAbove futureBudget
  rw [source_transaction_memzero,evaluateHOLFiniteState_seq_line780,run]
  dsimp only
  refine ⟨?_,Nat.le_trans bounded.2.1 remaining,bounded.2.2⟩
  change state.clock ≤ _ + (401 + transactionTypedSuffixCost inputLength.toNat inputLength.toNat)
  change state.clock ≤ post.clock + 400 + 1 at spent
  have rest := bounded.1
  omega

#print axioms source_transaction_memzero
#print axioms transaction_memzero_suffix_heap_bounded
end InitECandidate.Runtime
