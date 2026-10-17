import InitECandidate.Runtime.ScratchAllocationSource
import InitECandidate.Runtime.TrapCallNoTimeout
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An oversized original scratch request takes trap_with(7) before any
frontier update; it terminates within one source tick and cannot return. -/
theorem evaluate_scratchAllocation_request_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (failed : (pointer - frame).toNat < size.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state scratchAllocationAfterPointer
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none ∧
      (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have sub : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "p"),.var .global (ofString "frame_mem_ptr")]) =
        some (.val (.word (pointer - frame))) := by
    simp [evalHOLExact,evalListHOLExact,pointerLocal,frameGlobal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have flag : Compiler.Encoders.Asm.wordCmpHOL .lower (pointer - frame) size = true := by
    change decide ((pointer - frame).toNat < size.toNat) = true
    exact decide_eq_true failed
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) scratchAllocationRequestCheck = some (.val (.word 1)) := by
    unfold scratchAllocationRequestCheck
    rw [evalHOLExact,sub]
    simp only [evalHOLExact,sizeLocal,flag]
    rfl
  have terminal := evaluate_trap_call_terminal state (.const 7) 7 code (by rfl)
  have safe := evaluate_trap_call_no_timeout state (.const 7) 7 (by omega) code (by rfl)
  have clock := evaluate_trap_call_clock state (.const 7) 7 code (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "trap_with") [.const 7]
  unfold scratchAllocationAfterPointer
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 7]) with
  | mk result post =>
    rw [run] at terminal safe clock noReturn
    dsimp only at terminal safe clock noReturn
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped => exact ⟨clock,safe,terminal,noReturn⟩

/-- The full original allocator body rejects insufficient requests within one
source tick, including restoration of its pointer declaration scope. -/
theorem evaluate_source_scratch_alloc_request_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (failed : (pointer - frame).toNat < size.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_scratch_alloc) = (result,post) ∧
      post.clock = state.clock - 1 ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result ≠ some (.returned value)) := by
  let entered := setVarHOLFinite (ofString "p") (.val (.word pointer)) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atSize : entered.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "p" ≠ ofString "n" by decide] using sizeLocal
  have bound := evaluate_scratchAllocation_request_failure entered pointer size frame atPointer atSize frameGlobal failed code ticks
  cases run : evaluateHOLFiniteState entered scratchAllocationAfterPointer with
  | mk result output =>
    rw [run] at bound
    dsimp only at bound
    let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "p",state.locals.lookup (ofString "p"))}
    refine ⟨result,post,?_,bound.1,bound.2.1,bound.2.2.1,bound.2.2.2⟩
    rw [source_scratch_alloc_body,evaluateHOLFiniteState_dec_total]
    have initial : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.var .global (ofString "scratch_ptr")) = some (.val (.word pointer)) := by
      simpa [evalHOLExact] using scratchGlobal
    simp only [initial,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered scratchAllocationAfterPointer; _) = _
    rw [run]

#print axioms evaluate_source_scratch_alloc_request_failure
#print axioms evaluate_scratchAllocation_request_failure
end InitECandidate.Runtime
