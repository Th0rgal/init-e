import InitECandidate.Runtime.SecpInitSuccess
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

/-- Repeated secp256k1_init: a nonzero scratch pointer returns 0 at once. -/
theorem evaluate_secp256k1Init_body_initialized {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch : BitVec 64) (installed : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word scratch)))
    (nonzero : scratch ≠ 0) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_secp256k1_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0)) = some (.val (.word 1)) := by
    simp [evalHOLExact,installed,Compiler.Encoders.Asm.wordCmpHOL]
    simpa using nonzero
  rw [source_secp256k1Init_body,evaluateHOLFiniteState_seq_line780]
  simp only [evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms evaluate_secp256k1Init_body_initialized

/-- The actual call `secp256k1_init()` on first initialization: four ticks,
caller locals restored, scratch arena installed at the entry heap pointer. -/
theorem evaluate_secp256k1Init_call_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (request : (448 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer 448).toNat ≤ 33806089496)
    (domainP : ∀ cell ∈ secpBlockCells 18446744069414583343 18446744073709551615 18446744073709551615 18446744073709551615,
      state.memaddrs (pointer + cell.1))
    (domainN : ∀ cell ∈ secpBlockCells 13822214165235122497 13451932020343611451 18446744073709551614 18446744073709551615,
      state.memaddrs (pointer + 160 + cell.1))
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "secp256k1_init") []) = (none,post) ∧
      post.clock = state.clock - 4 ∧ post.memory = secpInitMemory state.memory pointer ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 448))) ∧
      (∀ watched, watched ≠ ofString "secp_accel_scratch" → watched ≠ ofString "heap_ptr" →
        post.globals.lookup watched = state.globals.lookup watched) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨bodyPost,body,ticks,memory,_,postCode,domain,endian,scratch,finalHeap,others⟩ :=
    evaluate_secp256k1Init_body_success entry pointer code heap zero request finishBound domainP domainN
      (by change 3 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "secp256k1_init")
    (sourceFunctionBody Guest.guestFn_secp256k1_init) (by rw [code]; exact originalRuntimeCode_secp256k1Init_lookup)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "secp256k1_init") [] []
    (sourceFunctionBody Guest.guestFn_secp256k1_init) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    args lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,?_,memory,rfl,postCode,domain,endian,scratch,finalHeap,others⟩
  change bodyPost.clock = state.clock - 1 - 3 at ticks
  change bodyPost.clock = state.clock - 4
  omega

#print axioms evaluate_secp256k1Init_call_success

theorem secpBlockCells_offset (m0 m1 m2 m3 : BitVec 64) :
    ∀ cell ∈ secpBlockCells m0 m1 m2 m3, cell.1.toNat ≤ 120 := by
  intro cell member
  simp only [secpBlockCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h <;> subst h <;> simp

/-- First secp256k1_init from any heap pointer with an accessible capped arena:
the allocation guards and all sixteen store domains follow from the arena. -/
theorem evaluate_secp256k1Init_call_from_arena {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)))
    (room : pointer.toNat + 455 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
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
  have cell : ∀ k : BitVec 64, k.toNat ≤ 280 → state.memaddrs (pointer + k) := by
    intro k hk
    apply arena
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
    · rw [BitVec.toNat_add_of_lt (by omega)]; omega
  obtain ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,others⟩ :=
    evaluate_secp256k1Init_call_success state pointer code heap zero request finish
      (fun c m => cell _ (by have := secpBlockCells_offset _ _ _ _ c m; omega))
      (fun c m => by
        rw [BitVec.add_assoc]
        exact cell _ (by
          have := secpBlockCells_offset _ _ _ _ c m
          rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega))
      budget
  exact ⟨post,run,clock,memory,locals,postCode,domain,endian,scratch,finalHeap,by simpa using covered,finish,aligned,others⟩

#print axioms evaluate_secp256k1Init_call_from_arena
end InitECandidate.Runtime
