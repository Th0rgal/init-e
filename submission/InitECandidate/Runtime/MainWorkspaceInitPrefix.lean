import InitECandidate.Runtime.AllocationInitializersCallSuccess
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_main_u256WorkspaceInit_call : mainAt 5 =
    .seq (.call (some (none,none)) (ofString "u256_ws_init") []) (mainAt 6) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_main_workspaceInit_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717640)))
    (zero : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0)))
    (budget : 2 ≤ state.clock) :
    ∃ next : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (mainAt 5) = evaluateHOLFiniteState next (mainAt 6) ∧
      next.clock = state.clock - 2 ∧ next.code = state.code ∧ next.memaddrs = state.memaddrs ∧
      next.locals = state.locals ∧ next.memory = state.memory ∧
      next.globals = globalAllocationGlobals state.globals 2713717640 u256WorkspaceAllocations ∧
      next.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718280)) := by
  obtain ⟨next,call,clock,memory,locals,installed,domain,globals,finalHeap⟩ :=
    evaluate_u256WorkspaceInit_call_success state 2713717640 code heap zero
      (by simp only [u256WorkspaceAllocations,List.map_cons,List.map_nil,AllocationPlanSafe]; decide) budget
  refine ⟨next,?_,clock,installed,domain,locals,memory,globals,?_⟩
  · rw [source_main_u256WorkspaceInit_call,evaluateHOLFiniteState_seq_line780,call]
  · simpa only [show allocationPlanEnd 2713717640 (u256WorkspaceAllocations.map Prod.snd) = 2713718280 by decide] using finalHeap

#print axioms source_main_u256WorkspaceInit_call
#print axioms evaluate_main_workspaceInit_prefix
end InitECandidate.Runtime
