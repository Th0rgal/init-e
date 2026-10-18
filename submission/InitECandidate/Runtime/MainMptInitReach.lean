import InitECandidate.Runtime.MptInitCallBound
import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.PanHandlerFreeCallControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def MptInitContinuation {F : Type} (state next : PanSemStateFiniteExact 64 F) : Prop :=
  next.globals = globalAllocationGlobals state.globals 2713717456 mptInitAllocations ∧
    next.code = state.code ∧ next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
    next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717640))

theorem source_main_mptInit_call : mainAt 4 =
    .seq (.call (some (none,none)) (ofString "mpt_init") []) (mainAt 5) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual main either reaches the next initializer with the computed heap
and globals, or terminates without returning in the same finite prefix bound. -/
theorem evaluate_main_mptInit_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456)))
    (words : ∀ entry ∈ mptInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (code : state.code = originalRuntimeCode) (budget : 725 ≤ state.clock)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    Reaches state (mainAt 4) (MptInitContinuation state) 725 (mainAt 5) := by
  have bounded := evaluate_mptInit_call_bounded state stateGlobal padGlobal heap words code budget arena
  rw [source_main_mptInit_call]
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_init") []) with
  | mk result next =>
    rw [run] at bounded
    dsimp only at bounded
    obtain ⟨cost,remaining,noTimeout,globals,installed,domain,locals⟩ := bounded
    cases result with
    | none =>
      left
      refine ⟨next,⟨globals,installed,domain,locals rfl,?_⟩,cost,remaining,rfl⟩
      rw [globals]
      exact (mptInit_allocation_globals state.globals).2.2.2
    | some result =>
      right
      refine ⟨result,rfl,?_,cost,remaining,?_⟩
      · intro value equal
        have consumed := (evaluate_handlerFree_call_control state none (ofString "mpt_init") []).2.2 value
        rw [run] at consumed
        exact consumed (by rw [equal])
      · intro _ equal
        exact noTimeout (by rw [equal])

#print axioms source_main_mptInit_call
#print axioms evaluate_main_mptInit_reaches
end InitECandidate.Runtime
