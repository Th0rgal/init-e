import InitECandidate.Runtime.GlobalAllocationPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def u256WorkspaceAllocations : List (MlS × BitVec 64) := [(ofString "u256_ws",640)]

theorem source_u256WorkspaceInit_body : sourceFunctionBody Guest.guestFn_u256_ws_init =
    .seq (.ite (.cmp .equal (.var .global (ofString "u256_ws")) (.const 0))
      (.call (some (some (.global,ofString "u256_ws"),none)) (ofString "alloc") [.const 640]) .skip)
      (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_u256WorkspaceInit_zero {F : Type} (state : PanSemStateFiniteExact 64 F)
    (zero : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_u256_ws_init) =
      evaluateHOLFiniteState state (globalAllocationProgram u256WorkspaceAllocations (.return (.const 0))) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .equal (.var .global (ofString "u256_ws")) (.const 0)) = some (.val (.word 1)) := by
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_u256WorkspaceInit_body]
  simp only [u256WorkspaceAllocations,globalAllocationProgram,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_ite,condition]
  rfl

/-- First workspace initialization allocates exactly the original 640 bytes.
The actual zero-global guard is discharged rather than assuming an allocation. -/
theorem evaluate_u256WorkspaceInit_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "u256_ws") = some (.val (.word 0)))
    (safe : AllocationPlanSafe pointer [640]) (budget : 1 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_u256_ws_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer u256WorkspaceAllocations ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 640))) := by
  rw [evaluate_u256WorkspaceInit_zero state zero]
  apply evaluate_globalAllocation_return state u256WorkspaceAllocations pointer code heap (by decide) ?_ safe budget
  intro entry member
  simp only [u256WorkspaceAllocations,List.mem_cons,List.not_mem_nil,or_false] at member
  subst entry
  exact ⟨0,zero⟩

#print axioms source_u256WorkspaceInit_body
#print axioms evaluate_u256WorkspaceInit_zero
#print axioms evaluate_u256WorkspaceInit_success
end InitECandidate.Runtime
