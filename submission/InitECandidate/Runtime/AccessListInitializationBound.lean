import InitECandidate.Runtime.AccessListLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessInitialized := accessAt 2

theorem source_access_initialized : accessInitialized =
    .dec (ofString "i") .one (.const 0) accessLoopAndReturn := by
  simp only [accessInitialized,accessLoopAndReturn,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_access_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame heap : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (heapBound : heap.toNat ≤ 33806089496) (heapAligned : heap.toNat % 8 = 0)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heap.toNat)
    (recordsBeforeHeap : records.toNat + count.toNat * 24 ≤ heap.toNat)
    (reserve : heap.toNat + (inputLength.toNat * 48 + 46) * count.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : count.toNat *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessInitialized
    state.clock ≤ evaluated.2.clock + count.toNat *
        (accessStepCost inputLength.toNat inputLength.toNat + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let initial := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have atList : initial.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "lst" by decide] using listLocal
  have atRecords : initial.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "recs" by decide] using recordsLocal
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initialSlices : RlpSliceInputPrefix initial array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state initial array slot p n input inputLength entry rfl rfl rfl⟩
  let valid : AccessLoopWitness initial array count records input inputLength scratch frame ceiling :=
    ⟨0,heap,atList,atRecords,atIndex,by simp,initialSlices,scratchGlobal,frameGlobal,heapGlobal,code,arena,
      heapArena,heapBound,heapAligned,inputBeforeHeap,recordsBeforeHeap,by simpa using reserve⟩
  have bound := evaluate_access_loop_and_return_bounded initial array count records input inputLength scratch frame ceiling inputLimit
    valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame
    (by change (count.toNat - 0) * _ ≤ state.clock; simpa only [Nat.sub_zero] using budget)
  rw [source_access_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState initial accessLoopAndReturn with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_access_initialized_bounded
end InitECandidate.Runtime
