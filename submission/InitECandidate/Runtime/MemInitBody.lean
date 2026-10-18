import InitECandidate.Runtime.AllocationSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_memInit_body : sourceFunctionBody Guest.guestFn_mem_init =
    .seq (.assign .global (ofString "heap_ptr") (.const 2713714688))
      (.seq (.assign .global (ofString "scratch_ptr") (.const 2713714688))
        (.seq (.assign .global (ofString "frame_mem_ptr") (.const 2701135872))
          (.return (.const 0)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def memInitReady {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word 2701135872))
    (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word 2713714688))
      (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word 2713714688)) state))

theorem evaluate_assign_global_constant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (old value : BitVec 64)
    (present : state.globals.lookup name = some (.val (.word old))) :
    evaluateHOLFiniteState state (.assign .global name (.const value)) =
      (none,setGlobalHOLFinite name (.val (.word value)) state) := by
  simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,
    lookupKvarHOLExact,present,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

/-- The first main initializer establishes the real heap and scratch layout
from word-shaped globals, without a fuel or memory-access premise. -/
theorem evaluate_memInit_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_mem_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite (memInitReady state)) := by
  rw [source_memInit_body]
  apply evaluate_seq_none (evaluate_assign_global_constant state _ oldHeap _ heap)
  apply evaluate_seq_none (evaluate_assign_global_constant _ _ oldScratch _ (by
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratch))
  apply evaluate_seq_none (evaluate_assign_global_constant _ _ oldFrame _ (by
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide,
      show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide] using frame))
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,memInitReady]

#print axioms source_memInit_body
#print axioms evaluate_assign_global_constant
#print axioms evaluate_memInit_body
end InitECandidate.Runtime
