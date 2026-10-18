import InitECandidate.Runtime.SecpInitCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

theorem evaluate_secp256k1Init_call_from_aligned_arena {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (pointerAligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + 455 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "secp256k1_init") []) = (none,post) ∧
      post.clock = state.clock - 4 ∧ post.memory = secpInitMemory state.memory pointer ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 448))) ∧
      pointer.toNat + 448 ≤ (allocationEnd pointer 448).toNat ∧
      (allocationEnd pointer 448).toNat ≤ 33806089496 ∧ (allocationEnd pointer 448).toNat % 8 = 0 ∧
      (∀ watched, watched ≠ ofString "secp_accel_scratch" → watched ≠ ofString "heap_ptr" →
        post.globals.lookup watched = state.globals.lookup watched) := by
  obtain ⟨request,finish,covered,aligned⟩ := allocation_success_bounds pointer 448 (by simpa using room)
  have offsetAligned : ∀ m0 m1 m2 m3 : BitVec 64, ∀ c ∈ secpBlockCells m0 m1 m2 m3, c.1.toNat % 8 = 0 := by
    intro m0 m1 m2 m3 c member
    simp only [secpBlockCells,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h|h|h <;> subst h <;> simp
  have cell : ∀ k : BitVec 64, k.toNat % 8 = 0 → k.toNat ≤ 280 → state.memaddrs (pointer + k) := by
    intro k aligned hk
    apply arena
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
  obtain ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,others⟩ :=
    evaluate_secp256k1Init_call_success state pointer code heap zero request finish
      (fun c m => cell _ (offsetAligned _ _ _ _ c m) (by have := secpBlockCells_offset _ _ _ _ c m; omega))
      (fun c m => by
        rw [BitVec.add_assoc]
        exact cell _ (by
          have := offsetAligned _ _ _ _ c m
          have := secpBlockCells_offset _ _ _ _ c m
          rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega) (by
          have := secpBlockCells_offset _ _ _ _ c m
          rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega))
      budget
  exact ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,by simpa using covered,finish,aligned,others⟩

#print axioms evaluate_secp256k1Init_call_from_aligned_arena
end InitECandidate.Runtime
