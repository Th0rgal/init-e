import InitECandidate.Runtime.Bn254InitActualHeap
import InitECandidate.Runtime.Bn254InitCallCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem evaluate_bn254Init_call_at_entry_heap_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)))
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713718728 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 35 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bn254_init") [])
    state.clock ≤ result.2.clock + 35 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = bn254InitGlobals state.globals 2713718728 ∧
        result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944)) ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs) := by
  obtain ⟨a,b,c,d⟩ := evaluate_bn254Init_call_outcome_cells state 2713718728 code heap (by decide) (by decide) (by decide)
    gammaZero paramsZero words b2Word expwWord (fun x aligned lo hi => arena x aligned (by simpa using lo) hi) budget
  refine ⟨a,b,c,fun normal => ?_⟩
  obtain ⟨g,l,k,m⟩ := d normal
  refine ⟨g,?_,l,k,m⟩
  rw [g,bn254InitGlobals_heap]
  rfl

#print axioms bn254InitGlobals_other
#print axioms evaluate_bn254Init_call_at_entry_heap_cells
end InitECandidate.Runtime
