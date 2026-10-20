import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.RunFramesConditions
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def frameMemoryAllocationEndExpression : ExpHOL 64 :=
  .op .and [.op .add [.var .local (ofString "p"),.var .local (ofString "n"),.const 7],
    .op .sub [.const 0,.const 8]]

def frameMemoryAllocationRequestCheck : ExpHOL 64 :=
  .cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"),.var .local (ofString "p")]) (.var .local (ofString "n"))

def frameMemoryAllocationFinish : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
    (.call (some (none,none)) (ofString "trap_with") [.const 6]) .skip)
    (.seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
      (.return (.var .local (ofString "p"))))

def frameMemoryAllocationAfterPointer : ProgHOL 64 :=
  .seq (.ite frameMemoryAllocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 6]) .skip)
    (.dec (ofString "q") .one frameMemoryAllocationEndExpression frameMemoryAllocationFinish)

theorem source_frame_mem_alloc_body : sourceFunctionBody Guest.guestFn_frame_mem_alloc =
    .dec (ofString "p") .one (.var .global (ofString "frame_mem_ptr")) frameMemoryAllocationAfterPointer := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_frame_mem_alloc,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,frameMemoryAllocationAfterPointer,frameMemoryAllocationRequestCheck,frameMemoryAllocationEndExpression,frameMemoryAllocationFinish]
  rfl

theorem eval_frameMemoryAllocationEndExpression {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) frameMemoryAllocationEndExpression =
        some (.val (.word (allocationEnd pointer size))) := by
  simp [frameMemoryAllocationEndExpression,evalHOLExact,evalListHOLExact,pointerLocal,sizeLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,allocationEnd,BitVec.add_assoc]
  change (pointer + (size + 7)) &&& ((0 - 8) &&& BitVec.allOnes 64) = _
  rw [BitVec.and_allOnes]
  rfl


#print axioms source_frame_mem_alloc_body
#print axioms eval_frameMemoryAllocationEndExpression
end InitECandidate.Runtime
