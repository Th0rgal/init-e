import InitECandidate.Runtime.ListHashLayoutHeapRestore
import InitECandidate.Runtime.HtrRequestsSuffixMemory
import InitECandidate.Runtime.HtrRequestsBodyBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrRequests_allocation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (ctx : HtrRequestsEntryContext state sha accelerator zeroHashes chunk record heap out)
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (budget : htrRequestsAllocationCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrRequestsAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let argument : ExpHOL 64 := .panop .mul [.const 5,.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (160#64))] := rfl
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "ch") heap (160#64) (htrRequestsAt 2)
    args ctx.code ctx.atHeap ctx.heapFits (by unfold htrRequestsAllocationCost at budget; omega)
  have source : htrRequestsAt 1 = .decCall (ofString "ch") .one (ofString "alloc") [argument] (htrRequestsAt 2) := rfl
  rw [← source] at reached
  obtain ⟨next,facts,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrRequestsAt 1) (htrRequestsAt 2)
    _ 2 value reached (by rw [run])
  obtain ⟨locals,memory,installed,domain,globals,cap,covers,aligned⟩ := facts
  have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have extent : heap.toNat + 160 ≤ (allocationEnd heap (160#64)).toNat := covers
  have recordLayout : ListHashMemoryLayout next sha accelerator zeroHashes chunk (allocationEnd heap (160#64)) heap record :=
    ⟨⟨(nonHeap _ (by decide)).trans ctx.atSha,(nonHeap _ (by decide)).trans ctx.atAccel,
      (nonHeap _ (by decide)).trans ctx.atZero,
      (by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),
      ctx.heapAligned,(by omega),Or.inl (by have := ctx.recordHeap; omega),aligned,cap,
      (by have := ctx.recordHeap; omega),ctx.accelAligned,(by have := ctx.accelRecord; have := ctx.recordHeap; omega),
      (by have := ctx.shaRecord; have := ctx.recordHeap; omega),Or.inr ctx.accelRecord,Or.inr ctx.shaRecord,
      installed.trans ctx.code⟩,(nonHeap _ (by decide)).trans ctx.atChunk,ctx.chunkAligned,
      (by have := ctx.chunkRecord; have := ctx.recordHeap; omega),Or.inr ctx.chunkRecord⟩
  have decoded : HtrRequestsDecoded next record := by
    intro index inside
    obtain ⟨p,n,entry,small⟩ := ctx.decoded index inside
    exact ⟨p,n,entry.after_frame state next record index p n domain (congrFun memory _) (congrFun memory _),small⟩
  have nextCtx : HtrRequestsContext next sha accelerator zeroHashes chunk record heap (allocationEnd heap (160#64)) out :=
    ⟨recordLayout,(keep _ (by decide)).trans ctx.atRecord,
      (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]),(keep _ (by decide)).trans ctx.atOut,
      decoded,(by omega),(by have := ctx.recordHeap; omega),ctx.recordHeap,ctx.shaRecord,ctx.accelRecord,ctx.chunkRecord⟩
  have nextLayout := layout.after_heap_restore globals installed aligned cap (by have := layout.heapBefore; omega)
  have remaining : htrRequestsCost2 ≤ next.clock := by
    change 2 + htrRequestsCost2 ≤ state.clock at budget
    omega
  have suffix := htrRequests_list0_memory next (evaluateHOLFiniteState next (htrRequestsAt 2)).2
    sha accelerator zeroHashes chunk record heap (allocationEnd heap (160#64)) out mark watched value nextCtx nextLayout
    ((keep _ (by decide)).trans atMark) layout.heapBefore remaining (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrRequestsAt 2)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,suffix]
  exact congrFun memory watched

#print axioms htrRequests_allocation_returned_memory
end InitECandidate.Runtime
