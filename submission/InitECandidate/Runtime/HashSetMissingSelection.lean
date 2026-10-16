import InitECandidate.Runtime.HashSetExisting
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The lookup sentinel selects the original missing-key continuation without
changing state or spending a source clock. -/
theorem evaluate_hashSet_missing_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity : BitVec 64) (missing : ProgHOL 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word capacity)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity) :
    evaluateHOLFiniteState state (hashSetExistingTail missing) = evaluateHOLFiniteState state missing := by
  have d16 : state.memaddrs (table + 16#64) := domain16
  have c16 : state.memory (table + 16#64) = .word capacity := cell16
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16))) =
      some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d16,c16,Compiler.Encoders.Asm.wordCmpHOL]
  unfold hashSetExistingTail
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_skip]

#print axioms evaluate_hashSet_missing_tail
end InitECandidate.Runtime
