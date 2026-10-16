import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.RunFramesConditions
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def allocationEndExpression : ExpHOL 64 :=
  .op .and [.op .add [.var .local (ofString "p"),.var .local (ofString "n"),.const 7],
    .op .sub [.const 0,.const 8]]

def allocationRequestCheck : ExpHOL 64 :=
  .cmp .lower (.op .sub [.const 33806089496,.var .local (ofString "p")]) (.var .local (ofString "n"))

def allocationFinish : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (.const 33806089496) (.var .local (ofString "q")))
    (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip)
    (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
      (.return (.var .local (ofString "p"))))

def allocationAfterPointer : ProgHOL 64 :=
  .seq (.ite allocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip)
    (.dec (ofString "q") .one allocationEndExpression allocationFinish)

theorem source_alloc_body : sourceFunctionBody Guest.guestFn_alloc =
    .dec (ofString "p") .one (.var .global (ofString "heap_ptr")) allocationAfterPointer := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_alloc,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,allocationAfterPointer,allocationRequestCheck,allocationEndExpression,allocationFinish]
  rfl

theorem eval_allocationEndExpression {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) allocationEndExpression =
        some (.val (.word (allocationEnd pointer size))) := by
  simp [allocationEndExpression,evalHOLExact,evalListHOLExact,pointerLocal,sizeLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,allocationEnd,BitVec.add_assoc]
  change (pointer + (size + 7)) &&& ((0 - 8) &&& BitVec.allOnes 64) = _
  rw [BitVec.and_allOnes]
  rfl

theorem eval_allocationRequestCheck {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) allocationRequestCheck =
        some (.val (.word 0)) := by
  classical
  have sub : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.const 33806089496,.var .local (ofString "p")]) =
        some (.val (.word ((33806089496 : BitVec 64) - pointer))) := by
    simp [evalHOLExact,evalListHOLExact,pointerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have sufficient : size.toNat ≤ (33806089496#64 - pointer).toNat := BitVec.le_def.mp request
  have flag : Compiler.Encoders.Asm.wordCmpHOL .lower ((33806089496 : BitVec 64) - pointer) size = false := by
    change decide (((33806089496 : BitVec 64) - pointer).toNat < size.toNat) = false
    exact decide_eq_false (Nat.not_lt.mpr (BitVec.le_def.mp request))
  unfold allocationRequestCheck
  rw [evalHOLExact,sub]
  simp only [evalHOLExact]
  rw [sizeLocal]
  simp only [flag]
  rfl

#print axioms eval_allocationRequestCheck

/-- Successful allocator finish changes the global pointer and returns the old
pointer, with no body clock tick or memory mutation. -/
theorem evaluate_allocationFinish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer finish oldHeap : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (finishLocal : state.locals.lookup (ofString "q") = some (.val (.word finish)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word oldHeap)))
    (within : finish.toNat ≤ 33806089496) :
    evaluateHOLFiniteState state allocationFinish =
      (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite
        (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word finish)) state)) := by
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.const 33806089496) (.var .local (ofString "q"))) = some (.val (.word 0)) := by
    simp [evalHOLExact,finishLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_lt.mpr within]
  unfold allocationFinish
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (0 : BitVec 64) = 0 from rfl,if_true,evaluateHOLFiniteState_skip]
  have assign : evaluateHOLFiniteState state
      (.assign .global (ofString "heap_ptr") (.var .local (ofString "q"))) =
        (none,setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word finish)) state) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,finishLocal,isValidValueHOLExact,
      lookupKvarHOLExact,heapGlobal,shapeOfHOLExact,shapeEqHOL]
  apply evaluate_seq_none assign
  simp [evaluateHOLFiniteState_return,evalHOLExact,pointerLocal,setKvarHOLFinite,setGlobalHOLFinite,shapeOfHOLExact]

#print axioms source_alloc_body
#print axioms eval_allocationEndExpression
#print axioms evaluate_allocationFinish
end InitECandidate.Runtime
