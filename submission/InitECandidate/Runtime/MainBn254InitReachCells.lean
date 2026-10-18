import InitECandidate.Runtime.MainBn254InitReach
import InitECandidate.Runtime.Bn254InitActualHeapCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem evaluate_main_bn254Init_reaches_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)))
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713718728 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 35 ≤ state.clock) :
    Reaches state (mainAt 7) (Bn254InitContinuation state) 35 (mainAt 8) := by
  have bounded := evaluate_bn254Init_call_at_entry_heap_cells state code heap gammaZero paramsZero words b2Word expwWord arena budget
  rw [source_main_bn254Init_call]
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bn254_init") []) with
  | mk result next =>
    rw [run] at bounded
    dsimp only at bounded
    obtain ⟨spent,remaining,noTimeout,normal⟩ := bounded
    cases result with
    | none =>
      obtain ⟨globals,heapEnd,locals,installed,domain⟩ := normal rfl
      exact Or.inl ⟨next,⟨globals,installed,domain,locals,heapEnd⟩,spent,remaining,rfl⟩
    | some result =>
      right
      refine ⟨result,rfl,?_,spent,remaining,?_⟩
      · intro value equal
        have consumed := evaluate_discard_call_no_return state (ofString "bn254_init") [] value
        rw [run] at consumed
        exact consumed (by rw [equal])
      · intro _ equal
        exact noTimeout (by rw [equal])

#print axioms source_main_bn254Init_call
#print axioms evaluate_main_bn254Init_reaches_cells
end InitECandidate.Runtime
