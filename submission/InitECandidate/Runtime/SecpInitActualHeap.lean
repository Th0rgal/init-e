import InitECandidate.Runtime.SecpInitCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem secpInit_actual_allocationEnd : allocationEnd 2713718280 448 = 2713718728 := by decide

/-- First secp256k1_init at the actual entry heap 2713718280 reached after the
first six main initializers: arena 2713718280..2713718728, four ticks. -/
theorem evaluate_secp256k1Init_call_at_entry_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718280)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (arena : ∀ address : BitVec 64, 2713718280 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "secp256k1_init") []) = (none,post) ∧
      post.clock = state.clock - 4 ∧ post.memory = secpInitMemory state.memory 2713718280 ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 2713718280)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)) ∧
      (∀ watched, watched ≠ ofString "secp_accel_scratch" → watched ≠ ofString "heap_ptr" →
        post.globals.lookup watched = state.globals.lookup watched) := by
  obtain ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,_,_,_,others⟩ :=
    evaluate_secp256k1Init_call_from_arena state 2713718280 code heap zero (by decide)
      (fun a lo hi => arena a (by simpa using lo) hi) budget
  rw [secpInit_actual_allocationEnd] at finalHeap
  exact ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,others⟩

#print axioms evaluate_secp256k1Init_call_at_entry_heap
end InitECandidate.Runtime
