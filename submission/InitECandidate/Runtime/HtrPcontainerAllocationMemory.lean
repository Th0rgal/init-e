import InitECandidate.Runtime.HtrPcontainerProgressiveMemory
import InitECandidate.Runtime.HtrPcontainerAllocationBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem htrPcontainer_allocation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap chunks out mark count watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 256) (budget : htrPcontainerAllocationCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPcontainerAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := evaluate_allocation_declaration_reaches state (.const 64) (ofString "tmp") heap (64#64)
    (htrPcontainerAt 2) rfl layout.code layout.atHeap layout.heapFits
    (by unfold htrPcontainerAllocationCost at budget; omega)
  rw [← source_htrPcontainer_alloc] at reached
  obtain ⟨next,allocated,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrPcontainerAt 1)
    (htrPcontainerAt 2) _ 2 value reached (by rw [run])
  obtain ⟨locals,memory,installed,_,globals,cap,covers,aligned⟩ := allocated
  change heap.toNat + 64 ≤ (allocationEnd heap (64#64)).toNat at covers
  have keep (key : MlS) (different : key ≠ ofString "tmp") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nextLayout : HashMemoryLayout next sha accelerator zeroHashes (allocationEnd heap (64#64)) out watched := {
    atSha := (nonHeap _ (by decide)).trans layout.atSha
    atAccel := (nonHeap _ (by decide)).trans layout.atAccel
    atZero := (nonHeap _ (by decide)).trans layout.atZero
    atHeap := by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
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
    code := installed.trans layout.code }
  have remaining : (progressiveBodyCost + 1) + (count.toNat + 135) ≤ next.clock := by
    have tailBound : count.toNat + 135 ≤ htrPcontainerSuffixCost := by
      change count.toNat + 135 ≤ 18446744073709551768
      omega
    change 2 + ((progressiveBodyCost + 1) + htrPcontainerSuffixCost) ≤ state.clock at budget
    generalize progressiveBodyCost = pc at budget ⊢
    generalize htrPcontainerSuffixCost = sc at tailBound budget
    omega
  have frame := htrPcontainer_progressive_returned_memory next (evaluateHOLFiniteState next (htrPcontainerAt 2)).2
    sha accelerator zeroHashes (allocationEnd heap (64#64)) chunks heap out mark count watched value nextLayout
    ((keep _ (by decide)).trans atChunks)
    (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide)).trans atOut) ((keep _ (by decide)).trans atMark) ((keep _ (by decide)).trans atCount)
    small layout.heapAligned (by change heap.toNat + 64 ≤ _; change heap.toNat + 64 ≤ _ at covers; omega)
    layout.heapBefore remaining (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (htrPcontainerAt 2)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,frame]
  exact congrFun memory watched

#print axioms htrPcontainer_allocation_returned_memory
end InitECandidate.Runtime
