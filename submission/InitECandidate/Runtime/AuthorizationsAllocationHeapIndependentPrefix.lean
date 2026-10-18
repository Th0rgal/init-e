import InitECandidate.Runtime.AuthorizationsAllocationIndependentPrefix
import InitECandidate.Runtime.AuthorizationsAllocationHeapBound
import InitECandidate.Runtime.AuthorizationsInitializationHeapIndependentPrefix
import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful record allocation retains the complete traversal output contract. -/
theorem authorization_allocation_returned_heap_independent_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (aligned : records.toNat % 8 = 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word records)))
    (heapBound : records.toNat ≤ 33806089496) (countBound : count.toNat * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, records.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeRecords : input.toNat + inputLength.toNat ≤ records.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (recordsAbove : ceiling ≤ records.toNat)
    (budget : count.toNat *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) + 2 ≤ state.clock)
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeRecords : watchedArray.toNat + watchedCount.toNat * 16 ≤ records.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state authorizationAfterSlices = (some (.returned value),final)) :
    RlpSliceInputPrefix final watchedArray input inputLength watchedCount.toNat := by
  let argument : ExpHOL 64 := .panop .mul [.rfield 1 (.var .local (ofString "lst")),.const 120]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 120))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,panOpHOL,valueIsWord,valueWord]
  rw [source_authorization_allocation] at run
  have request := alloc_declaration_returned_request state final argument records (count * 120) (ofString "recs") .one
    authorizationInitialized value args code heap run
  obtain ⟨ready,_,clock,memory,locals,readyCode,domain,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state argument records
    (count * 120) args code (by omega) heap request (allocationEnd_within_heap records (count * 120) heapBound request)
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
  have interval := allocationGuard_sum_bound records (count * 120) heapBound request
  have product : (count * 120).toNat = count.toNat * 120 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 120 < 2^64; exact countBound)]
    rfl
  rw [product] at interval
  have nextNat : (allocationEnd records (count * 120)).toNat = records.toNat + count.toNat * 120 := by
    have sizeAligned : (count * 120).toNat % 8 = 0 := by rw [product]; omega
    rw [allocationEnd_aligned_toNat records (count * 120) (by rw [product]; exact interval) aligned sizeAligned,product]
  have atHeap : entered.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd records (count * 120)))) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredHeapArena : ∀ address : BitVec 64, (allocationEnd records (count * 120)).toNat ≤ address.toNat →
      address.toNat < 33806089496 → entered.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain]
    exact heapArena address (by rw [nextNat] at lower; omega) upper
  have allocationBounds := allocationEnd_covers records (count * 120) (by rw [product]; exact interval)
  change evaluateHOLFiniteState state (.decCall (ofString "recs") .one (ofString "alloc") [argument] authorizationInitialized) = _ at run
  rw [decl] at run
  cases tailRun : evaluateHOLFiniteState entered authorizationInitialized with
  | mk result output =>
    rw [tailRun] at run
    have same : result = some (.returned value) := (Prod.mk.inj run).1
    subst result
    have enteredWatched : RlpSliceInputPrefix entered watchedArray input inputLength watchedCount.toNat := by
      intro slot inside
      obtain ⟨p,n,item⟩ := watchedValid slot inside
      exact ⟨p,n,item.after_frame state entered watchedArray slot p n input inputLength domain (congrFun memory _) (congrFun memory _)⟩
    have retained := authorization_initialized_returned_heap_independent_prefix entered output array count records input inputLength scratch frame
      (allocationEnd records (count * 120)) ceiling inputLimit atList atRecords enteredSlices atScratch atFrame
      (readyCode.trans code) enteredArena atHeap enteredHeapArena (allocationEnd_within_heap records (count * 120) heapBound request)
      allocationBounds.2.2 (by rw [nextNat]; omega) (by rw [nextNat]) (by rw [nextNat]; omega)
      inputBound limitBound orderedFrame framePositive scratchBelow arrayFits arrayAbove arrayBeforeRecords countLimit inputBeforeFrame
      (by
        change count.toNat * (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ ready.clock
        rw [clock]
        exact Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) budget))
      watchedArray watchedCount enteredWatched watchedFits watchedAbove watchedBeforeRecords value tailRun
    have restored := (Prod.mk.inj run).2
    rw [← restored]
    intro slot inside
    obtain ⟨p,n,item⟩ := retained slot inside
    exact ⟨p,n,item.after_frame output _ watchedArray slot p n input inputLength rfl rfl rfl⟩

#print axioms authorization_allocation_returned_heap_independent_prefix
end InitECandidate.Runtime
