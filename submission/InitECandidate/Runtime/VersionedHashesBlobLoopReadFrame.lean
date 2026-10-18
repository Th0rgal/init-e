import InitECandidate.Runtime.VersionedHashesBlobReadFrame
import InitECandidate.Runtime.VersionedHashesBlobLocals
import InitECandidate.Runtime.NormalWhileInvariant
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original blob loop preserves memory and globals at
any count and fuel. No readable-header or alignment assumption is needed. -/
theorem versioned_hashes_blob_loop_normal_read_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx index vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state versionedHashesBlobLoop = (none,post)) :
    post.memory = state.memory ∧ post.globals = state.globals := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    ∃ j k : BitVec 64,
      current.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      current.locals.lookup (ofString "j") = some (.val (.word j)) ∧
      current.locals.lookup (ofString "vh") = some (.val (.word vh)) ∧
      current.locals.lookup (ofString "k") = some (.val (.word k)) ∧
      current.code = originalRuntimeCode ∧ current.memory = state.memory ∧ current.globals = state.globals
  have initial : invariant state := ⟨index,cursor,txLocal,indexLocal,vhLocal,cursorLocal,code,rfl,rfl⟩
  have step : ∀ current output, invariant current →
      evaluateHOLFiniteState current versionedHashesBlobStep = (none,output) → invariant output := by
    rintro current output ⟨j,k,atTx,atJ,atVh,atK,original,memory,globals⟩ bodyRun
    have frame := versioned_hashes_blob_step_typed_read_frame current tx j vh k atTx atJ atVh atK original
    rw [bodyRun] at frame
    have metadata := evaluateHOLFiniteState_metadata current versionedHashesBlobStep
    rw [bodyRun] at metadata
    exact ⟨j + 1,k + 1,(versioned_hashes_blob_step_tx_frame current output bodyRun).trans atTx,
      versioned_hashes_blob_step_adds_one current output j atJ bodyRun,
      (versioned_hashes_blob_step_vh_frame current output bodyRun).trans atVh,
      versioned_hashes_blob_step_k_adds_one current output k atK bodyRun,
      metadata.1.trans original,frame.1.trans memory,frame.2.trans globals⟩
  rw [source_versioned_hashes_blob_loop] at run
  have done := evaluate_normal_while_invariant versionedHashesBlobCondition versionedHashesBlobStep invariant
    (by rintro current ⟨j,k,atTx,atJ,atVh,atK,original,memory,globals⟩;
        exact ⟨j,k,atTx,atJ,atVh,atK,original,memory,globals⟩)
    step (by rw [source_versioned_hashes_blob_step]; rfl) state post initial run
  obtain ⟨j,k,_,_,_,_,_,memory,globals⟩ := done
  exact ⟨memory,globals⟩

#print axioms versioned_hashes_blob_loop_normal_read_frame
end InitECandidate.Runtime
