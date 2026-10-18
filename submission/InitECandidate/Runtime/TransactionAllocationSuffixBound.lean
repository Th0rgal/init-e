import InitECandidate.Runtime.TransactionMemzeroSuffixBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationAligned
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionAllocationSuffixCost (inputLength : Nat) : Nat :=
  1 + transactionMemzeroSuffixCost inputLength

theorem source_transaction_allocation : transactionAt 2 =
    .decCall (ofString "tx") .one (ofString "alloc") [.const 400] (transactionAt 3) := by
  simp only [transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_allocation_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame tx kind : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (positive : 0 < inputLength.toNat) (noWrap : input.toNat + inputLength.toNat < 2^64)
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
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionAllocationSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 2)
    state.clock ≤ evaluated.2.clock + transactionAllocationSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let array := allocationEnd tx 400
  have arrayNat : array.toNat = tx.toNat + 400 := by
    exact allocationEnd_aligned_toNat tx 400 txBound txAligned (by decide)
  have arrayBound : array.toNat ≤ 33806089496 := by rw [arrayNat]; exact txBound
  have ticks : 1 + transactionMemzeroSuffixCost inputLength.toNat ≤ state.clock := budget
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 400] =
      some [.val (.word (400 : BitVec 64))] := by rfl
  obtain ⟨ready,_,clock,memory,locals,postCode,domain,shapes,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state (.const 400) tx 400 args code (by omega) heap
      (allocationGuard_of_sum_bound tx 400 txBound) arrayBound
  let middle := setVarHOLFinite (ofString "tx") (.val (.word tx)) ready
  have atTx : middle.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have kept : ∀ key, key ≠ ofString "tx" → middle.locals.lookup key = state.locals.lookup key := by
    intro key different
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have heapReady : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word array)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simp [array,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have scratchReady : middle.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratchGlobal
  have frameReady : middle.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using frameGlobal
  have futureBudget : transactionMemzeroSuffixCost inputLength.toNat ≤ middle.clock := by
    change _ ≤ ready.clock
    omega
  have bounded := transaction_memzero_suffix_bounded middle input inputLength scratch frame array tx kind ceiling inputLimit
    ((kept _ (by decide)).trans pointerLocal) ((kept _ (by decide)).trans lengthLocal) positive noWrap inputBound limitBound
    scratchReady frameReady (postCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; change ready.memaddrs address; rw [domain]; exact arena address low high)
    heapReady arrayBound countLimit
    (by intro address low high; change ready.memaddrs address; rw [domain]; apply heapArena address _ high; rw [arrayNat] at low; omega)
    inputBeforeFrame (by rw [arrayNat]; omega) atTx ((kept _ (by decide)).trans byteLocal) (by rw [arrayNat]; omega)
    (by rw [arrayNat]; exact reserve) txBound txAligned
    (by intro address low high; change ready.memaddrs address; rw [domain]; exact heapArena address low (Nat.lt_of_lt_of_le high txBound)) futureBudget
  rw [source_transaction_allocation,decl]
  change state.clock ≤ (evaluateHOLFiniteState middle (transactionAt 3)).2.clock + transactionAllocationSuffixCost inputLength.toNat ∧
    (evaluateHOLFiniteState middle (transactionAt 3)).2.clock ≤ state.clock ∧ _
  refine ⟨?_,?_,bounded.2.2⟩
  · have spent := bounded.1
    change ready.clock ≤ _ + _ at spent
    change state.clock ≤ _ + (1 + transactionMemzeroSuffixCost inputLength.toNat)
    omega
  · have remaining := bounded.2.1
    change _ ≤ ready.clock at remaining
    omega

#print axioms source_transaction_allocation
#print axioms transaction_allocation_suffix_bounded
end InitECandidate.Runtime
