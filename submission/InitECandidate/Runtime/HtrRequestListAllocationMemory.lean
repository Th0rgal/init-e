import InitECandidate.Runtime.HtrRequestListSuffixMemory
import InitECandidate.Runtime.HtrRequestListBodyBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequestList_allocation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk kind pointer size count heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (inputs : RequestListInputs state kind pointer size count out)
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (small : count.toNat ≤ 134217712) (budget : htrRequestListAllocationCost count ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrRequestListAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let argument : ExpHOL 64 := .op .add [.panop .mul [.var .local (ofString "n"),.const 32],.const 32]
  let bytes := count * (32#64) + (32#64)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word bytes)] := by
    simp [argument,bytes,evalListHOLExact,evalHOLExact,inputs.countLocal,panOpHOL,wordOpHOL,wordOp,
      isWfShapeExactHOL,valueIsWord,valueWord]
  have allocated := evaluate_allocation_declaration_reaches state argument (ofString "roots") heap bytes
    (htrRequestListAt 2) args layout.code layout.atHeap layout.heapFits
    (by change 2 + htrRequestListSuffixCost count ≤ state.clock at budget; omega)
  rw [← source_htrRequestList_alloc] at allocated
  have reached := reaches_trans state (htrRequestListAt 1) (htrRequestListAt 2) (htrRequestListAt 3)
    (AllocationDeclarationReady state (ofString "roots") heap bytes)
    (fun next => ∃ ready, AllocationDeclarationReady state (ofString "roots") heap bytes ready ∧
      next = setVarHOLFinite (ofString "i") (.val (.word (0#64))) ready) 2 0 allocated (by
      intro ready facts
      rw [source_htrRequestList_zero]
      apply reaches_dec
      intro v evaluated
      have same : v = .val (.word (0#64)) := Option.some.inj evaluated.symm
      subst v
      exact ⟨0#64,rfl,ready,facts,rfl⟩)
  obtain ⟨next,⟨ready,facts,equal⟩,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrRequestListAt 1)
    (htrRequestListAt 3) _ 2 value reached (by rw [run])
  obtain ⟨locals,memory,installed,_,globals,cap,covers,aligned⟩ := facts
  have keep (key : MlS) (ni : key ≠ ofString "i") (nr : key ≠ ofString "roots") :
      next.locals.lookup key = state.locals.lookup key := by
    rw [equal]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nr]
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
    rw [equal]
    change ready.globals.lookup key = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have mulNat : (count * (32#64)).toNat = count.toNat * 32 :=
    BitVec.toNat_mul_of_lt (by change count.toNat * 32 < 2 ^ 64; omega)
  have bytesNat : bytes.toNat = count.toNat * 32 + 32 := by
    change (count * (32#64) + (32#64)).toNat = _
    rw [BitVec.toNat_add_of_lt (by rw [mulNat]; change count.toNat * 32 + 32 < 2 ^ 64; omega),mulNat]
    rfl
  have nextLayout : ListHashMemoryLayout next sha accelerator zeroHashes chunk (allocationEnd heap bytes) out watched := {
    atSha := (nonHeap _ (by decide)).trans layout.atSha
    atAccel := (nonHeap _ (by decide)).trans layout.atAccel
    atZero := (nonHeap _ (by decide)).trans layout.atZero
    atHeap := by rw [equal]; change ready.globals.lookup _ = _; rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    outAligned := layout.outAligned
    outFits := layout.outFits
    outOutside := layout.outOutside
    heapAligned := aligned
    heapFits := cap
    heapBefore := by have := layout.heapBefore; omega
    accelAligned := layout.accelAligned
    accelFits := layout.accelFits
    shaFits := layout.shaFits
    accelOutside := layout.accelOutside
    shaOutside := layout.shaOutside
    code := by rw [equal]; exact installed.trans layout.code
    atChunk := (nonHeap _ (by decide)).trans layout.atChunk
    chunkAligned := layout.chunkAligned
    chunkFits := layout.chunkFits
    chunkOutside := layout.chunkOutside }
  have valid : HtrRequestListState kind pointer size heap (allocationEnd heap bytes) count next count.toNat := {
    heapGlobal := nextLayout.atHeap
    pointerLocal := (keep _ (by decide) (by decide)).trans inputs.pointerLocal
    kindLocal := (keep _ (by decide) (by decide)).trans inputs.kindLocal
    sizeLocal := (keep _ (by decide) (by decide)).trans inputs.sizeLocal
    rootsLocal := by rw [equal]; simp (config := {decide := true}) [setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE]
    countLocal := (keep _ (by decide) (by decide)).trans inputs.countLocal
    cursor := ⟨0#64,by rw [equal]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp⟩ }
  have frame := htrRequestList_suffix_returned_memory next (evaluateHOLFiniteState next (htrRequestListAt 3)).2
    sha accelerator zeroHashes chunk kind pointer size heap (allocationEnd heap bytes) count out mark watched value nextLayout valid
    ((keep _ (by decide) (by decide)).trans inputs.outLocal) ((keep _ (by decide) (by decide)).trans atMark) small layout.heapAligned
    (by rw [bytesNat] at covers; omega) layout.heapBefore
    (by change 2 + htrRequestListSuffixCost count ≤ state.clock at budget; omega) (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrRequestListAt 3)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,frame,equal]
  exact congrFun memory watched

#print axioms htrRequestList_allocation_returned_memory
end InitECandidate.Runtime
