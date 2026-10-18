import InitECandidate.Runtime.AllocationInitializersSuccess
import InitECandidate.Runtime.U256WorkspaceInitSuccess
import InitECandidate.Runtime.OriginalSha256InitCode
import InitECandidate.Runtime.OriginalKeccakInitCode
import InitECandidate.Runtime.OriginalU256WsInitCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_sha256Init_call_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ sha256InitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (sha256InitAllocations.map Prod.snd))
    (budget : 4 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "sha256_init") []) = (none,post) ∧
      post.clock = state.clock - 4 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer sha256InitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (sha256InitAllocations.map Prod.snd)))) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨bodyPost,body,ticks,memory,_,installed,domain,globals,finalHeap⟩ :=
    evaluate_sha256Init_body_success entry pointer code heap words safe
      (by change 3 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "sha256_init")
    (sourceFunctionBody Guest.guestFn_sha256_init)
    (by rw [code]; exact originalRuntimeCode_sha256Init_lookup)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "sha256_init") [] []
    (sourceFunctionBody Guest.guestFn_sha256_init) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    args lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,?_,memory,rfl,installed,domain,globals,finalHeap⟩
  change bodyPost.clock = state.clock - 4
  change bodyPost.clock = state.clock - 1 - 3 at ticks
  omega

#print axioms evaluate_sha256Init_call_success

theorem evaluate_keccakInit_call_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (keccakInitAllocations.map Prod.snd))
    (budget : 3 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak_init") []) = (none,post) ∧
      post.clock = state.clock - 3 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer keccakInitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (keccakInitAllocations.map Prod.snd)))) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨bodyPost,body,ticks,memory,_,installed,domain,globals,finalHeap⟩ :=
    evaluate_keccakInit_body_success entry pointer code heap words safe
      (by change 2 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "keccak_init")
    (sourceFunctionBody Guest.guestFn_keccak_init)
    (by rw [code]; exact originalRuntimeCode_keccakInit_lookup)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "keccak_init") [] []
    (sourceFunctionBody Guest.guestFn_keccak_init) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    args lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,?_,memory,rfl,installed,domain,globals,finalHeap⟩
  change bodyPost.clock = state.clock - 3
  change bodyPost.clock = state.clock - 1 - 2 at ticks
  omega

#print axioms evaluate_keccakInit_call_success

theorem evaluate_u256WorkspaceInit_call_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0)))
    (safe : AllocationPlanSafe pointer (u256WorkspaceAllocations.map Prod.snd))
    (budget : 2 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "u256_ws_init") []) = (none,post) ∧
      post.clock = state.clock - 2 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer u256WorkspaceAllocations ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (u256WorkspaceAllocations.map Prod.snd)))) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨bodyPost,body,ticks,memory,_,installed,domain,globals,finalHeap⟩ :=
    evaluate_u256WorkspaceInit_success entry pointer code heap zero safe
      (by change 1 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "u256_ws_init")
    (sourceFunctionBody Guest.guestFn_u256_ws_init)
    (by rw [code]; exact originalRuntimeCode_u256WsInit_lookup)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "u256_ws_init") [] []
    (sourceFunctionBody Guest.guestFn_u256_ws_init) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    args lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,?_,memory,rfl,installed,domain,globals,finalHeap⟩
  change bodyPost.clock = state.clock - 2
  change bodyPost.clock = state.clock - 1 - 1 at ticks
  omega

#print axioms evaluate_u256WorkspaceInit_call_success

end InitECandidate.Runtime
