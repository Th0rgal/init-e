import InitECandidate.Runtime.AccessListAllocationHeapBound
import InitECandidate.Runtime.AccessListInitializationHeapIndependentOuterPrefix
import InitECandidate.Runtime.AllocationReturnedGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful record allocation retains the complete traversal output contract. -/
theorem access_allocation_returned_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (aligned : records.toNat % 8 = 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word records)))
    (heapBound : records.toNat ≤ 33806089496) (countBound : count.toNat * 24 < 2^64)
    (heapArena : ∀ address : BitVec 64, records.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeRecords : input.toNat + inputLength.toNat ≤ records.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : count.toNat *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) + 2 ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state accessAfterSlices = (some (.returned value),final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let argument : ExpHOL 64 := .panop .mul [.rfield 1 (.var .local (ofString "lst")),.const 24]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 24))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,panOpHOL,valueIsWord,valueWord]
  rw [source_access_allocation] at run
  have request := alloc_declaration_returned_request state final argument records (count * 24) (ofString "recs") .one
    accessInitialized value args code heap run
  obtain ⟨ready,_,clock,memory,locals,readyCode,domain,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state argument records
    (count * 24) args code (by omega) heap request (allocationEnd_within_heap records (count * 24) heapBound request)
  let entered := setVarHOLFinite (ofString "recs") (.val (.word records)) ready
  have atList : entered.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "recs" ≠ ofString "lst" by decide] using listLocal
  have atRecords : entered.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredSlices : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entered array slot p n input inputLength item domain (congrFun memory _) (congrFun memory _)⟩
  have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratchGlobal
  have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using frameGlobal
  have enteredArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → entered.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain]
    exact arena address lower upper
  have interval := allocationGuard_sum_bound records (count * 24) heapBound request
  have product : (count * 24).toNat = count.toNat * 24 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 24 < 2^64; exact countBound)]
    rfl
  rw [product] at interval
  have nextNat : (allocationEnd records (count * 24)).toNat = records.toNat + count.toNat * 24 := by
    have sizeAligned : (count * 24).toNat % 8 = 0 := by rw [product]; omega
    rw [allocationEnd_aligned_toNat records (count * 24) (by rw [product]; exact interval) aligned sizeAligned,product]
  have atHeap : entered.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd records (count * 24)))) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredHeapArena : ∀ address : BitVec 64, (allocationEnd records (count * 24)).toNat ≤ address.toNat →
      address.toNat < 33806089496 → entered.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain]
    exact heapArena address (by rw [nextNat] at lower; omega) upper
  have allocationBounds := allocationEnd_covers records (count * 24) (by rw [product]; exact interval)
  change evaluateHOLFiniteState state (.decCall (ofString "recs") .one (ofString "alloc") [argument] accessInitialized) = _ at run
  rw [decl] at run
  cases tailRun : evaluateHOLFiniteState entered accessInitialized with
  | mk result output =>
    rw [tailRun] at run
    have same : result = some (.returned value) := (Prod.mk.inj run).1
    subst result
    have enteredWatched : RlpSliceInputPrefix entered watchedArray watchedInput watchedLength watchedCount.toNat := by
      intro slot inside
      obtain ⟨p,n,item⟩ := watchedValid slot inside
      exact ⟨p,n,item.after_frame state entered watchedArray slot p n watchedInput watchedLength domain (congrFun memory _) (congrFun memory _)⟩
    have retained := access_initialized_returned_heap_independent_outer_prefix entered output array count records input inputLength scratch frame
      (allocationEnd records (count * 24)) ceiling inputLimit atList atRecords enteredSlices atScratch atFrame
      (readyCode.trans code) enteredArena atHeap enteredHeapArena (allocationEnd_within_heap records (count * 24) heapBound request)
      allocationBounds.2.2 (by rw [nextNat]; omega) (by rw [nextNat])
      inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame
      (by
        change count.toNat * (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ ready.clock
        rw [clock]
        exact Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) budget))
      watchedArray watchedCount watchedInput watchedLength enteredWatched watchedAbove watchedBeforeRecords value tailRun
    have restored := (Prod.mk.inj run).2
    rw [← restored]
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms access_allocation_returned_heap_independent_outer_prefix
end InitECandidate.Runtime
