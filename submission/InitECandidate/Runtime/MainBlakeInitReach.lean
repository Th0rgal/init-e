import InitECandidate.Runtime.Blake2InitReturned
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def BlakeInitContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = blake2InitGlobals state.globals 2713730208 ∧ next.code = state.code ∧
    next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730616))

theorem source_main_blakeInit_call : mainAt 10 =
    .seq (.call (some (none,none)) (ofString "blake2_init") []) (mainAt 11) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Main reaches header initialization with the actual BLAKE2 globals and
heap, or terminates early, within seven source ticks. -/
theorem evaluate_main_blakeInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730208)))
    (sigmaZero : state.globals.lookup (ofString "b2_sigma") = some (.val (.word 0)))
    (words : ∀ name ∈ [ofString "b2_iv",ofString "b2_round",ofString "b2_v",ofString "b2_m"],
      ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (budget : 7 ≤ state.clock) :
    Reaches state (mainAt 10) (BlakeInitContinuation state) 7 (mainAt 11) := by
  have bounded := evaluate_blake2Init_call_at_entry_heap state code heap sigmaZero words budget
  rw [source_main_blakeInit_call]
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "blake2_init") []) with
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
        have consumed := evaluate_discard_call_no_return state (ofString "blake2_init") [] value
        rw [run] at consumed
        exact consumed (by rw [equal])
      · intro _ equal
        exact noTimeout (by rw [equal])

#print axioms source_main_blakeInit_call
#print axioms evaluate_main_blakeInit_reaches
end InitECandidate.Runtime
