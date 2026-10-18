import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.AllocationPlanAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def ripemdInitAllocations : List (MlS × BitVec 64) :=
  [(ofString "rmd_tab",160),(ofString "rmd_x",128),(ofString "rmd_h",40),(ofString "rmd_pad",128)]

def ripemdInitAfterGuard : ProgHOL 64 := statelessNext (structuralFunctionBody Guest.guestFn_ripemd160_init)

theorem source_ripemdInit_body : sourceFunctionBody Guest.guestFn_ripemd160_init =
    .seq (.ite (.cmp .notEqual (.var .global (ofString "rmd_tab")) (.const 0)) (.return (.const 0)) .skip)
      ripemdInitAfterGuard := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_store_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (output : ValueHOL 64) :
    (evaluateHOLFiniteState state (.store destination value)).1 ≠ some (.returned output) := by
  have control := (evaluate_store_control_frame state destination value).1
  rcases control with equal | equal <;> rw [equal] <;> simp

theorem ripemdInit_globals_fragment : AllocationFramedGlobals ripemdInitAfterGuard ripemdInitAllocations := by
  repeat first
    | exact AllocationFramedGlobals.finish
    | apply AllocationFramedGlobals.allocation
    | apply AllocationFramedGlobals.framed _ (originalGlobalsFrame_leaf _ (fun _ => rfl))
        (by intro F state value; exact evaluate_store_no_return state _ _ value)

/-- A first RIPEMD initialization that returns installs the exact four
allocation globals and advances the heap by 456 bytes. Store failures are
excluded only by the actual returned execution. -/
theorem evaluate_ripemdInit_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "rmd_tab") = some (.val (.word 0)))
    (words : ∀ entry ∈ ripemdInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 456 ≤ 33806089496)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ripemd160_init) =
      (some (.returned value),post)) :
    value = .val (.word 0) ∧ post.globals = globalAllocationGlobals state.globals pointer ripemdInitAllocations ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        finalHeap.toNat = pointer.toNat + 456 := by
  have guard : evaluateHOLFiniteState state
      (.ite (.cmp .notEqual (.var .global (ofString "rmd_tab")) (.const 0)) (.return (.const 0)) .skip) =
      (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [source_ripemdInit_body,evaluateHOLFiniteState_seq_line780,guard] at run
  have alignedSizes : ∀ size ∈ ripemdInitAllocations.map Prod.snd, size.toNat % 8 = 0 := by
    intro size member
    simp only [ripemdInitAllocations,List.map_cons,List.map_nil,Prod.snd,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have plan := allocationPlan_safe_aligned (ripemdInitAllocations.map Prod.snd) pointer aligned alignedSizes
    (by simpa [ripemdInitAllocations] using small)
  have names : ∀ entry ∈ ripemdInitAllocations, entry.1 ≠ ofString "heap_ptr" := by decide
  obtain ⟨returnedZero,globals⟩ := ripemdInit_globals_fragment.returned state post pointer value code heap names words plan.1 run
  refine ⟨returnedZero,globals,allocationPlanEnd pointer (ripemdInitAllocations.map Prod.snd),?_,?_⟩
  · rw [globals]
    exact globalAllocationGlobals_heap_frontier state.globals pointer ripemdInitAllocations heap names
  · simpa [ripemdInitAllocations] using plan.2

#print axioms source_ripemdInit_body
#print axioms ripemdInit_globals_fragment
#print axioms evaluate_ripemdInit_body_returned_globals
end InitECandidate.Runtime
