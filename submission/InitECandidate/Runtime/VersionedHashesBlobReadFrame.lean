import InitECandidate.Runtime.VersionedHashesBlobStepBound
import InitECandidate.Runtime.MemeqReadFrame
import InitECandidate.Runtime.PanDecCallReadFrame
import InitECandidate.Runtime.PanThreeValueLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual hash comparisons and their local-only continuation never change
memory or globals, including timeout, shape failure and early returns. -/
theorem versioned_hashes_blob_step_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      versionedHashesCompareArguments = some [.val (.word left),.val (.word right),.val (.word (32 : BitVec 64))]) :
    let output := evaluateHOLFiniteState state versionedHashesBlobStep
    output.2.memory = state.memory ∧ output.2.globals = state.globals := by
  have lookup := pan_three_value_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memeq) (.word left) (.word right) (.word 32)
    (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_memeq_lookup)
  have compared := evaluate_decCall_readOnly_frame state (ofString "eq") (ofString "memeq") .one .one
    versionedHashesCompareArguments [.val (.word left),.val (.word right),.val (.word (32 : BitVec 64))]
    (sourceFunctionBody Guest.guestFn_memeq) versionedHashesCompareTail _ args lookup memeq_readOnlyMemory (by rfl)
  rw [source_versioned_hashes_blob_step,evaluateHOLFiniteState_seq_line780]
  unfold versionedHashesBlobGuard
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      exact compared
    · rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      split_ifs <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem versioned_hashes_blob_step_missing_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      versionedHashesCompareArguments = none) :
    let output := evaluateHOLFiniteState state versionedHashesBlobStep
    output.2.memory = state.memory ∧ output.2.globals = state.globals := by
  have failed := evaluateHOLFiniteState_decCall_args_none state (ofString "eq") .one (ofString "memeq")
    versionedHashesCompareArguments versionedHashesCompareTail args
  rw [source_versioned_hashes_blob_step,evaluateHOLFiniteState_seq_line780]
  unfold versionedHashesBlobGuard
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      rw [failed]
      exact ⟨rfl,rfl⟩
    · rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      split_ifs <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

theorem versioned_hashes_blob_step_typed_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx j vh k : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (jLocal : state.locals.lookup (ofString "j") = some (.val (.word j)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (kLocal : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (code : state.code = originalRuntimeCode) :
    let output := evaluateHOLFiniteState state versionedHashesBlobStep
    output.2.memory = state.memory ∧ output.2.globals = state.globals := by
  classical
  by_cases domain : state.memaddrs (tx + 256#64)
  · cases cell : state.memory (tx + 256#64) with
    | word buffer =>
      apply versioned_hashes_blob_step_read_frame state (buffer + j * 32) (vh + k * 32) code
      simp [versionedHashesCompareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
          txLocal,jLocal,vhLocal,kLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,
          isWfShapeExactHOL,memLoadHOLExact,List.map_cons,List.map_nil,domain,cell]
  · have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        versionedHashesCompareArguments = none := by
      simp [versionedHashesCompareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
        txLocal,jLocal,vhLocal,kLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,
        isWfShapeExactHOL,memLoadHOLExact,List.map_cons,List.map_nil,domain]
    have failed := versioned_hashes_blob_step_missing_read_frame state args
    exact failed

#print axioms versioned_hashes_blob_step_missing_read_frame
#print axioms versioned_hashes_blob_step_typed_read_frame
#print axioms versioned_hashes_blob_step_read_frame
end InitECandidate.Runtime
