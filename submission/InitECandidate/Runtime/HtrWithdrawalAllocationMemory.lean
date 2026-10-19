import InitECandidate.Runtime.HtrWithdrawalCallsMemory
import InitECandidate.Runtime.HtrWithdrawalAllocationBound
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrWithdrawal_allocation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes w heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atW : state.locals.lookup (ofString "w") = some (.val (.word w)))
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrWithdrawalAllocationCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrWithdrawalAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reached := evaluate_allocation_declaration_reaches state (.panop .mul [.const 4,.const 32])
    (ofString "ch") heap (128#64) (htrWithdrawalAt 2) rfl code hh heapFits
    ((Nat.le_add_right 2 _).trans budget)
  rw [← source_htrWithdrawal_alloc] at reached
  obtain ⟨next,allocated,spent,_,agreement,normal⟩ := reaches_returned_continuation state (htrWithdrawalAt 1)
    (htrWithdrawalAt 2) _ 2 value reached (by rw [run])
  have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
    rw [allocated.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globals := allocated.2.2.2.2.1
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") :
      next.globals.lookup key = state.globals.lookup key := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atNewHeap : next.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd heap (128#64)))) := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atRoots : next.locals.lookup (ofString "ch") = some (.val (.word heap)) := by
    rw [allocated.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have covers : heap.toNat + 128 ≤ (allocationEnd heap (128#64)).toNat := allocated.2.2.2.2.2.2.1
  have enough : withdrawalCallsCost ≤ next.clock := by
    change 2 + withdrawalCallsCost ≤ state.clock at budget
    omega
  have frame := htrWithdrawal_calls_suffix_returned_memory next
    (evaluateHOLFiniteState next (htrWithdrawalAt 2)).2 pointer accelerator zeroHashes w heap
    (allocationEnd heap (128#64)) out mark watched value
    ((keep _ (by decide)).trans atW) heapAligned (by have cap := allocated.2.2.2.2.2.1; omega) heapBefore
    ((nonHeap _ (by decide)).trans atPointer) ((nonHeap _ (by decide)).trans atAccel)
    ((keep _ (by decide)).trans atMark) ((nonHeap _ (by decide)).trans atZero) atRoots atNewHeap
    ((keep _ (by decide)).trans atOut) outAligned outFits outOutside
    allocated.2.2.2.2.2.2.2 allocated.2.2.2.2.2.1 (by omega) accelAligned accelFits pointerFits
    accelOutside pointerOutside (allocated.2.2.1.trans code) enough (Prod.ext normal rfl)
  have memory : post.memory = (evaluateHOLFiniteState next (htrWithdrawalAt 2)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [memory,frame]
  exact congrFun allocated.2.1 watched

#print axioms htrWithdrawal_allocation_returned_memory
end InitECandidate.Runtime
