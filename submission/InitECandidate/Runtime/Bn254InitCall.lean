import InitECandidate.Runtime.Bn254InitReturned
import InitECandidate.Runtime.Bn254InitBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 4000000

/-- The actual call `bn254_init()` on first initialization from aligned heap H:
it never times out and spends at most 35 ticks; if it continues normally, the
globals are exactly `bn254InitGlobals` and caller locals, code and memory
domain are preserved. Any other outcome is an early abort (allocation trap,
inaccessible memory or an accelerator FFI final event). -/
theorem evaluate_bn254Init_call_outcome {F : Type} (state : PanSemStateFiniteExact 64 F) (H : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (aligned : H.toNat % 8 = 0) (positive : 0 < H.toNat) (room : H.toNat + 2048 ≤ 33806089496)
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, H.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 35 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bn254_init") [])
    state.clock ≤ result.2.clock + 35 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = bn254InitGlobals state.globals H ∧ result.2.locals = state.locals ∧
        result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs) := by
  have bounded := evaluate_bn254Init_call_bounded state none [] code budget
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_⟩
  intro normal
  have lookup := pan_no_args_lookup state.code.lookup (ofString "bn254_init")
    (sourceFunctionBody Guest.guestFn_bn254_init) (by rw [code]; exact originalRuntimeCode_bn254Init_lookup)
  have nonzero : state.clock ≠ 0 := by omega
  revert normal
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [lookup]
  simp only [if_neg nonzero]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_bn254_init) with
  | mk result post =>
    rcases result with _ | (_ | _ | _ | _ | w | _ | _)
    all_goals first
      | (simp; done)
      | skip
    have entryArena : ∀ address : BitVec 64, H.toNat ≤ address.toNat → address.toNat < 33806089496 →
        (callEntryStateHOLFinite state HolFiniteMapExact.empty).memaddrs address := arena
    obtain ⟨_,globals⟩ := bn254Init_body_returned (callEntryStateHOLFinite state HolFiniteMapExact.empty) post H w
      code heap aligned positive room gammaZero paramsZero words b2Word expwWord entryArena
      (by change 4 ≤ state.clock - 1; omega) run
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_bn254_init)
    rw [run] at meta'
    dsimp only
    split
    · intro _
      exact ⟨globals,rfl,meta'.1,meta'.2.1⟩
    · simp

#print axioms evaluate_bn254Init_call_outcome
end InitECandidate.Runtime
