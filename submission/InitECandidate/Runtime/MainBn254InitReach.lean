import InitECandidate.Runtime.Bn254InitActualHeap
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def Bn254InitContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = bn254InitGlobals state.globals 2713718728 ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944))

theorem source_main_bn254Init_call : mainAt 7 =
    .seq (.call (some (none,none)) (ofString "bn254_init") []) (mainAt 8) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual main reaches BLS initialization with BN254's computed heap and
globals, or terminates early, within the all-outcome 35-tick call bound. -/
theorem evaluate_main_bn254Init_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)))
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, 2713718728 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 35 ≤ state.clock) :
    Reaches state (mainAt 7) (Bn254InitContinuation state) 35 (mainAt 8) := by
  have bounded := evaluate_bn254Init_call_at_entry_heap state code heap gammaZero paramsZero words b2Word expwWord arena budget
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
#print axioms evaluate_main_bn254Init_reaches
end InitECandidate.Runtime
