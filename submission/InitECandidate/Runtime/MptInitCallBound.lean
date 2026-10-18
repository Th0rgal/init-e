import InitECandidate.Runtime.MptInitBodyBound
import InitECandidate.Runtime.OriginalMptInitCode
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.DiscardCallBodyGlobals
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual MPT call, including entry and every terminal outcome. The caller
receives exactly the globals computed by its five guarded allocations. -/
theorem evaluate_mptInit_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456)))
    (words : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (code : state.code = originalRuntimeCode) (budget : 725 ≤ state.clock)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_init") [])
    state.clock ≤ evaluated.2.clock + 725 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      evaluated.2.globals = globalAllocationGlobals state.globals 2713717456 mptInitAllocations ∧
      evaluated.2.code = state.code ∧ evaluated.2.memaddrs = state.memaddrs ∧
      (evaluated.1 = none → evaluated.2.locals = state.locals) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have bounded := evaluate_mptInit_body_bounded entry stateGlobal padGlobal heap words code
    (by change 724 ≤ state.clock - 1; omega) arena
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_mpt_init) with
  | mk result post =>
    rw [run] at bounded
    dsimp only at bounded
    obtain ⟨cost,remaining,noTimeout,globals⟩ := bounded
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
    have lookup := pan_no_args_lookup state.code.lookup (ofString "mpt_init")
      (sourceFunctionBody Guest.guestFn_mpt_init) (by rw [code]; exact originalRuntimeCode_mptInit_lookup)
    have call := evaluate_call_body_clock_no_timeout state post (ofString "mpt_init") none [] []
      (sourceFunctionBody Guest.guestFn_mpt_init) HolFiniteMapExact.empty .one result args lookup (by omega) run noTimeout
    have callGlobals := evaluate_discard_body_globals state post (ofString "mpt_init") [] []
      (sourceFunctionBody Guest.guestFn_mpt_init) HolFiniteMapExact.empty .one result args lookup (by omega) run
    have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "mpt_init") [])
    refine ⟨?_,?_,call.1,callGlobals.trans globals,metadata.1,metadata.2.1,?_⟩
    · rw [call.2]
      change state.clock - 1 ≤ post.clock + 724 at cost
      omega
    · rw [call.2]
      change post.clock ≤ state.clock - 1 at remaining
      omega
    · exact evaluate_discard_call_success_locals state (ofString "mpt_init") []

#print axioms evaluate_mptInit_call_bounded
end InitECandidate.Runtime
