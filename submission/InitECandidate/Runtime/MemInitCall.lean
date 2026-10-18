import InitECandidate.Runtime.MemInitBody
import InitECandidate.Runtime.OriginalMemInitCode
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The first actual call in main costs one source tick and establishes the
fixed allocator/scratch layout while retaining caller locals and memory. -/
theorem evaluate_memInit_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mem_init") []) =
      (none,{memInitReady {state with clock := state.clock - 1} with locals := state.locals}) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body := evaluate_memInit_body entry oldHeap oldScratch oldFrame heap scratch frame
  have installed : state.code.lookup (ofString "mem_init") =
      some ([],sourceFunctionBody Guest.guestFn_mem_init,.one) := by
    rw [code]
    exact originalRuntimeCode_memInit_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "mem_init") (sourceFunctionBody Guest.guestFn_mem_init) installed
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := rfl
  exact evaluateHOLFiniteState_call_return_caller_locals state none (ofString "mem_init") [] []
    (sourceFunctionBody Guest.guestFn_mem_init) HolFiniteMapExact.empty .one (.val (.word 0))
    (emptyLocalsHOLFinite (memInitReady entry)) args lookup ticks body
    (by simp [shapeOfHOLExact,shapeEqHOL])

theorem source_main_memInit_call : mainAt 0 =
    .seq (.call (some (none,none)) (ofString "mem_init") []) (mainAt 1) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_main_memInit_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (oldHeap oldScratch oldFrame : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word oldFrame)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    evaluateHOLFiniteState state (mainAt 0) =
      evaluateHOLFiniteState {memInitReady {state with clock := state.clock - 1} with locals := state.locals} (mainAt 1) := by
  rw [source_main_memInit_call,evaluateHOLFiniteState_seq_line780,
    evaluate_memInit_call state oldHeap oldScratch oldFrame heap scratch frame code ticks]

#print axioms evaluate_memInit_call
#print axioms source_main_memInit_call
#print axioms evaluate_main_memInit_prefix
end InitECandidate.Runtime
