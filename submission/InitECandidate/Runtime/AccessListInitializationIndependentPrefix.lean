import InitECandidate.Runtime.AccessListInitializationBound
import InitECandidate.Runtime.AccessListLoopReturnIndependentPrefix
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual index scope retains traversal output memory and global contracts. -/
theorem access_initialized_returned_independent_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock)
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessInitialized = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray input inputLength watchedCount.toNat := by
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
  rw [source_access_initialized] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0 accessLoopAndReturn
    (some (.returned value)) (by rfl) run
  have ticks : (count.toNat - valid.index.toNat) * (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ initial.clock := by
    change (count.toNat - 0) * _ ≤ state.clock
    simpa only [Nat.sub_zero] using budget
  have initialWatched : RlpSliceInputPrefix initial watchedArray input inputLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state initial watchedArray slot p n input inputLength rfl rfl rfl⟩
  have retained := access_loop_returned_independent_prefix initial output array count records input inputLength scratch frame ceiling inputLimit
    watchedArray watchedCount initialWatched watchedBeforeFrame watchedBeforeRecords valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayBeforeFrame arrayBeforeRecords countLimit inputBeforeFrame ticks value bodyRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n input inputLength rfl rfl rfl⟩

#print axioms access_initialized_returned_independent_prefix
end InitECandidate.Runtime
