import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def stateRestoreDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_state_restore with | .function fn => fn.body | _ => .skip

def stateRestoreLoopBody : ProgHOL 64 :=
  match stateRestoreDecodedBody with | .seq (.while _ body) _ => body | _ => .skip

def stateRestoreApplyRecord : ProgHOL 64 :=
  match stateRestoreLoopBody with | .seq _ applyRecord => applyRecord | _ => .skip

def stateRestoreDecrement : ProgHOL 64 :=
  .assign .global (ofString "journal_n")
    (.op .sub [.var .global (ofString "journal_n"),.const 1])

def stateRestoreCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "snap")) (.var .global (ofString "journal_n"))

theorem source_stateRestore_body : sourceFunctionBody Guest.guestFn_state_restore =
    .seq (.while stateRestoreCondition stateRestoreLoopBody) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [stateRestoreLoopBody,stateRestoreDecodedBody,stateRestoreCondition,Guest.guestFn_state_restore,
    declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,
    expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  rfl

theorem stateRestore_loop_body_shape : stateRestoreLoopBody =
    .seq stateRestoreDecrement stateRestoreApplyRecord := by
  simp only [stateRestoreLoopBody,stateRestoreDecodedBody,stateRestoreApplyRecord,stateRestoreDecrement,
    Guest.guestFn_state_restore,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  rfl

/-- The original journal loop decrements its global counter before applying
    the undo record. The assignment does not consume a source clock. -/
theorem evaluate_stateRestore_decrement {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    evaluateHOLFiniteState state stateRestoreDecrement =
      (none,setKvarHOLFinite .global (ofString "journal_n") (.val (.word (count - 1))) state) := by
  classical
  simp [stateRestoreDecrement,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,
    countGlobal,wordOpHOL,wordOp,valueIsWord,valueWord,isValidValueHOLExact,lookupKvarHOLExact,
    shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,setGlobalHOLFinite]

/-- A true journal guard rules out wraparound of the word decrement; the
    remaining undo count is a strictly decreasing natural-number rank. -/
theorem stateRestore_rank_decreases (count snapshot : BitVec 64)
    (guard : snapshot.toNat < count.toNat) :
    (count - 1).toNat = count.toNat - 1 ∧
      (count - 1).toNat - snapshot.toNat < count.toNat - snapshot.toNat := by
  have positive : 1 ≤ count.toNat := by omega
  have decrement : (count - 1).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · exact BitVec.le_def.mpr positive
  exact ⟨decrement,by omega⟩

/-- No journal work remains once the counter is at or below the snapshot.
    This source body returns immediately at any clock, including zero. -/
theorem evaluate_stateRestore_done {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count snapshot : BitVec 64)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (done : count.toNat ≤ snapshot.toNat) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_restore) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite state) := by
  rw [source_stateRestore_body,evaluateHOLFiniteState_seq_line780]
  have loop : evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (none,state) := by
    rw [evaluateHOLFiniteState_while_total]
    simp [stateRestoreCondition,evalHOLFinite,evalHOLExact,countGlobal,snapshotLocal,
      Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Nat.not_lt.mpr done]
  rw [loop]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms source_stateRestore_body
#print axioms stateRestore_loop_body_shape
#print axioms evaluate_stateRestore_decrement
#print axioms stateRestore_rank_decreases
#print axioms evaluate_stateRestore_done
end InitECandidate.Runtime
