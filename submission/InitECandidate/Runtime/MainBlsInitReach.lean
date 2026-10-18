import InitECandidate.Runtime.BlsPrecompilesInitSuccess
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def BlsInitContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = blsInitGlobals state.globals 2713719944 ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752))

theorem source_main_blsInit_call : mainAt 8 =
    .seq (.call (some (none,none)) (ofString "bls_precompiles_init") []) (mainAt 9) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual main completes first BLS initialization within 114 ticks, reaching
RIPEMD initialization with the exact BLS globals and heap frontier. -/
theorem evaluate_main_blsInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944)))
    (discountZero : state.globals.lookup (ofString "bls_discount") = some (.val (.word 0)))
    (constsZero : state.globals.lookup (ofString "bls_c") = some (.val (.word 0)))
    (fpZero : state.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0)))
    (fp2Zero : state.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0)))
    (g1Zero : state.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ blsLibWordNames, ∃ word : BitVec 64,
      state.globals.lookup name = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, 2713719944 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 114 ≤ state.clock) :
    Reaches state (mainAt 8) (BlsInitContinuation state) 114 (mainAt 9) := by
  obtain ⟨next,call,spent,remaining,locals,installed,domain,globals,heapEnd⟩ :=
    evaluate_blsPrecompilesInit_call_at_entry_heap state code heap discountZero constsZero fpZero fp2Zero g1Zero words arena budget
  refine Or.inl ⟨next,⟨globals,installed,domain,locals,heapEnd⟩,spent,remaining,?_⟩
  rw [source_main_blsInit_call,evaluateHOLFiniteState_seq_line780,call]
  exact scoped_refl _

#print axioms source_main_blsInit_call
#print axioms evaluate_main_blsInit_reaches
end InitECandidate.Runtime
