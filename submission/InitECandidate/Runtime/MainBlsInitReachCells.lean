import InitECandidate.Runtime.MainBlsInitReach
import InitECandidate.Runtime.BlsPrecompilesInitSuccessCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
theorem evaluate_main_blsInit_reaches_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944)))
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64,
      state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713719944 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 114 ≤ state.clock) :
    Reaches state (mainAt 8) (BlsInitContinuation state) 114 (mainAt 9) := by
  obtain ⟨next,call,spent,remaining,locals,installed,domain,globals,heapEnd⟩ :=
    evaluate_blsPrecompilesInit_call_at_entry_heap_cells state code heap discountZero constsZero fpZero fp2Zero g1Zero words arena budget
  refine Or.inl ⟨next,⟨globals,installed,domain,locals,heapEnd⟩,spent,remaining,?_⟩
  rw [source_main_blsInit_call,evaluateHOLFiniteState_seq_line780,call]
  exact scoped_refl _

#print axioms source_main_blsInit_call
#print axioms evaluate_main_blsInit_reaches_cells
end InitECandidate.Runtime
