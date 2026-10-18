import InitECandidate.Runtime.SszInitCallSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem evaluate_sszInit_after_hash_initializers_aligned {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713715312)))
    (zero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (words : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713715312 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_init") []) = (none,post) ∧
      post.clock = state.clock - 4 ∧ post.memory = memWrites state.memory 2713715408 sszInitCells ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals 2713715312 sszInitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456)) ∧
      post.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344)) ∧
      post.globals.lookup (ofString "zero_hashes") = some (.val (.word 2713715408)) := by
  have hashPointer : sszInitHashPointer 2713715312 = 2713715408 := by decide
  have cellsSmall : ∀ cell ∈ sszInitCells, cell.1.toNat < 2048 := by decide
  have cellsAligned : ∀ cell ∈ sszInitCells, cell.1.toNat % 8 = 0 := by decide
  have domain : ∀ cell ∈ sszInitCells, state.memaddrs (sszInitHashPointer 2713715312 + cell.1) := by
    intro cell member
    rw [hashPointer]
    have small := cellsSmall cell member
    have aligned := cellsAligned cell member
    have address : ((2713715408 : BitVec 64) + cell.1).toNat = 2713715408 + cell.1.toNat := by
      apply BitVec.toNat_add_of_lt
      change 2713715408 + cell.1.toNat < 2 ^ 64
      omega
    apply arena _ <;> rw [address] <;> omega
  obtain ⟨post,run,clock,memory,locals,installed,addresses,globals,finalHeap,offsets,hashes⟩ :=
    evaluate_sszInit_call_success state 2713715312 code heap zero words
      (by simp only [sszInitAllocations,List.map_cons,List.map_nil,AllocationPlanSafe]; decide) domain budget
  refine ⟨post,run,clock,?_,locals,installed,addresses,globals,?_,?_,?_⟩
  · simpa only [hashPointer] using memory
  · simpa only [show allocationEnd (sszInitHashPointer 2713715312) 2048 = 2713717456 by decide] using finalHeap
  · simpa only [show allocationEnd 2713715312 32 = 2713715344 by decide] using offsets
  · simpa only [hashPointer] using hashes

#print axioms evaluate_sszInit_after_hash_initializers_aligned
end InitECandidate.Runtime
