import InitECandidate.Runtime.AllocationSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def scratchAllocationEnd (pointer size : BitVec 64) : BitVec 64 := (pointer - size) &&& (0 - 8)

def scratchAllocationEndExpression : ExpHOL 64 :=
  .op .and [.op .sub [.var .local (ofString "p"),.var .local (ofString "n")],.op .sub [.const 0,.const 8]]

def scratchAllocationRequestCheck : ExpHOL 64 :=
  .cmp .lower (.op .sub [.var .local (ofString "p"),.var .global (ofString "frame_mem_ptr")]) (.var .local (ofString "n"))

def scratchAllocationFinish : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
    (.call (some (none,none)) (ofString "trap_with") [.const 7]) .skip)
    (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
      (.return (.var .local (ofString "q"))))

def scratchAllocationAfterPointer : ProgHOL 64 :=
  .seq (.ite scratchAllocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 7]) .skip)
    (.dec (ofString "q") .one scratchAllocationEndExpression scratchAllocationFinish)

theorem source_scratch_alloc_body : sourceFunctionBody Guest.guestFn_scratch_alloc =
    .dec (ofString "p") .one (.var .global (ofString "scratch_ptr")) scratchAllocationAfterPointer := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq,
    scratchAllocationAfterPointer,scratchAllocationRequestCheck,scratchAllocationEndExpression,scratchAllocationFinish]
  rfl

theorem eval_scratchAllocationEndExpression {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) scratchAllocationEndExpression =
        some (.val (.word (scratchAllocationEnd pointer size))) := by
  simp [scratchAllocationEndExpression,evalHOLExact,evalListHOLExact,pointerLocal,sizeLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,scratchAllocationEnd]
  change (pointer - size) &&& ((0 - 8) &&& BitVec.allOnes 64) = _
  rw [BitVec.and_allOnes]
  rfl

theorem eval_scratchAllocationRequestCheck {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size frame : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : size ≤ pointer - frame) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) scratchAllocationRequestCheck =
        some (.val (.word 0)) := by
  have sub : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "p"),.var .global (ofString "frame_mem_ptr")]) =
        some (.val (.word (pointer - frame))) := by
    simp [evalHOLExact,evalListHOLExact,pointerLocal,frameGlobal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have flag : Compiler.Encoders.Asm.wordCmpHOL .lower (pointer - frame) size = false := by
    change decide ((pointer - frame).toNat < size.toNat) = false
    exact decide_eq_false (Nat.not_lt.mpr (BitVec.le_def.mp request))
  unfold scratchAllocationRequestCheck
  rw [evalHOLExact,sub]
  simp only [evalHOLExact]
  rw [sizeLocal]
  simp only [flag]
  rfl

/-- A successful scratch finish updates the descending frontier and returns
its new value, without a body clock tick or memory write. -/
theorem evaluate_scratchAllocationFinish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (finish oldScratch frame : BitVec 64)
    (finishLocal : state.locals.lookup (ofString "q") = some (.val (.word finish)))
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word oldScratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (within : frame ≤ finish) :
    evaluateHOLFiniteState state scratchAllocationFinish =
      (some (.returned (.val (.word finish))),emptyLocalsHOLFinite
        (setKvarHOLFinite .global (ofString "scratch_ptr") (.val (.word finish)) state)) := by
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) = some (.val (.word 0)) := by
    simp [evalHOLExact,finishLocal,frameGlobal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,
      Nat.not_lt.mpr (BitVec.le_def.mp within)]
  unfold scratchAllocationFinish
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [if_true,evaluateHOLFiniteState_skip]
  have assign : evaluateHOLFiniteState state
      (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q"))) =
        (none,setKvarHOLFinite .global (ofString "scratch_ptr") (.val (.word finish)) state) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,finishLocal,isValidValueHOLExact,
      lookupKvarHOLExact,scratchGlobal,shapeOfHOLExact,shapeEqHOL]
  apply evaluate_seq_none assign
  simp [evaluateHOLFiniteState_return,evalHOLExact,finishLocal,setKvarHOLFinite,setGlobalHOLFinite,shapeOfHOLExact]

#print axioms source_scratch_alloc_body
#print axioms eval_scratchAllocationEndExpression
#print axioms eval_scratchAllocationRequestCheck
#print axioms evaluate_scratchAllocationFinish
end InitECandidate.Runtime
