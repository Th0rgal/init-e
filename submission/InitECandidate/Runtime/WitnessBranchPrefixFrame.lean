import InitECandidate.Runtime.WitnessBranchSource
import InitECandidate.Runtime.ArithmeticExpressionWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessBranchChildStore : ProgHOL 64 :=
  match witnessBranchAt 2 with | .seq first _ => first | _ => .skip

def witnessBranchOccupancyUpdate : ProgHOL 64 :=
  match witnessBranchAt 3 with | .seq first _ => first | _ => .skip

theorem source_witness_branch_child_store_sequence : witnessBranchAt 2 =
  .seq witnessBranchChildStore (witnessBranchAt 3) := by
  simp only [witnessBranchChildStore,source_witness_branch_child_store]

theorem source_witness_branch_occupancy_sequence : witnessBranchAt 3 =
  .seq witnessBranchOccupancyUpdate (witnessBranchAt 4) := by
  simp only [witnessBranchOccupancyUpdate,source_witness_branch_occupancy]

theorem source_witness_branch_child_store_fragment : witnessBranchChildStore =
  .store (.op .add [.var .local (ofString "br"),.const 32,
    .panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "result")) := by
  simp only [witnessBranchChildStore,source_witness_branch_child_store]

theorem source_witness_branch_occupancy_fragment : witnessBranchOccupancyUpdate =
  .ite (.cmp .notEqual (.var .local (ofString "result")) (.const 0))
    (.store (.op .add [.var .local (ofString "top"),.const 40])
      (.op .add [.load .one (.op .add [.var .local (ofString "top"),.const 40]),.const 1])) .skip := by
  simp only [witnessBranchOccupancyUpdate,source_witness_branch_occupancy]

theorem witness_branch_child_store_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (branch index result watched : BitVec 64)
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (separate : watched ≠ branch+32+index*8) :
    (evaluateHOLFiniteState s witnessBranchChildStore).2.memory watched = s.memory watched := by
  rw [source_witness_branch_child_store_fragment]
  apply evaluate_wordStore_memory_frame s _ _ (branch+32+index*8) watched
  · simp [evalHOLExact,evalListHOLExact,atBr,atIndex,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,BitVec.add_assoc]
  · intro parsed evaluated
    exact ⟨result,by simpa [evalHOLExact,atResult] using evaluated.symm⟩
  · exact separate

theorem witness_branch_occupancy_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top watched : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (separate : watched ≠ top+40) :
    (evaluateHOLFiniteState s witnessBranchOccupancyUpdate).2.memory watched = s.memory watched := by
  have frame := evaluate_wordStore_memory_frame s
    (.op .add [.var .local (ofString "top"),.const 40])
    (.op .add [.load .one (.op .add [.var .local (ofString "top"),.const 40]),.const 1]) (top+40) watched
    (by simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun parsed evaluated => eval_binop_returns_word s _ _ parsed evaluated) separate
  rw [source_witness_branch_occupancy_fragment,evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
    · exact frame
  · rfl

#print axioms source_witness_branch_child_store_sequence
#print axioms source_witness_branch_occupancy_sequence
#print axioms witness_branch_child_store_word_frame
#print axioms witness_branch_occupancy_word_frame
end InitECandidate.Runtime
