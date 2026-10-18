import InitECandidate.Runtime.HeaderInitCallSuccess
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.HeaderInitBodySuccessCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_headerInit_call_success_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0)))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + 8 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → pointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 11 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "header_init") []) = (none,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ ZeroBytePrefix post pointer 8 ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals.lookup (ofString "hdr_zero8") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 8))) ∧
      (∀ key, key ≠ ofString "hdr_zero8" → key ≠ ofString "heap_ptr" →
        post.globals.lookup key = state.globals.lookup key) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨bodyPost,body,cost,remaining,covered,_,installed,domain,header,finalHeap,other⟩ :=
    evaluate_headerInit_body_success_cells entry pointer code heap zero aligned room arena
      (by change 10 ≤ state.clock - 1; omega)
  have lookup := pan_no_args_lookup state.code.lookup (ofString "header_init")
    (sourceFunctionBody Guest.guestFn_header_init) (by rw [code]; exact originalRuntimeCode_headerInit_lookup)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "header_init") [] []
    (sourceFunctionBody Guest.guestFn_header_init) HolFiniteMapExact.empty .one (.val (.word 0)) bodyPost
    args lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,?_,?_,covered,rfl,installed,domain,header,finalHeap,other⟩
  · change state.clock ≤ bodyPost.clock + 11
    change state.clock - 1 ≤ bodyPost.clock + 10 at cost
    omega
  · change bodyPost.clock ≤ state.clock
    change bodyPost.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_headerInit_call_success_cells
end InitECandidate.Runtime
