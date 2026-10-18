import InitECandidate.Runtime.VersionedHashesIndexProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def versionedHashesCompareArguments : List (ExpHOL 64) :=
  [.op .add [.load .one (.op .add [.var .local (ofString "tx"),.const 256]),.panop .mul [.var .local (ofString "j"),.const 32]],
   .op .add [.var .local (ofString "vh"),.panop .mul [.var .local (ofString "k"),.const 32]],.const 32]
def versionedHashesCompareTail : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0)) (.return (.const 0)) .skip)
    (.seq (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1]))
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])))
def versionedHashesBlobGuard : ProgHOL 64 :=
  .ite (.cmp .notLower (.var .local (ofString "k")) (.var .local (ofString "nvh"))) (.return (.const 0)) .skip

theorem source_versioned_hashes_blob_step : versionedHashesBlobStep =
    .seq versionedHashesBlobGuard
      (.decCall (ofString "eq") .one (ofString "memeq") versionedHashesCompareArguments versionedHashesCompareTail) := by
  simp only [versionedHashesBlobGuard,versionedHashesCompareArguments,versionedHashesCompareTail,versionedHashesBlobStep,
    versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,versionedHashesAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A normally completed original comparison advances its blob index by one;
capacity rejection and unequal hashes instead leave through early returns. -/
theorem versioned_hashes_blob_step_adds_one : NormalLocalAdd (ofString "j") 1 versionedHashesBlobStep := by
  rw [source_versioned_hashes_blob_step]
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    exact evaluate_normalLocalFrame (ofString "j") versionedHashesBlobGuard (by rfl) state post run
  · apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
    unfold versionedHashesCompareTail
    apply normalLocalAdd_seq_normal_frame
    · intro F state post run
      exact evaluate_normalLocalFrame (ofString "j") _ (by rfl) state post run
    · apply normalLocalAdd_seq _ _ _ _ (by decide)
      exact normalLocalAdd_assign _ 1

theorem versioned_hashes_blob_step_count_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    post.locals.lookup (ofString "nb") = state.locals.lookup (ofString "nb") := by
  apply evaluate_normalLocalFrame (ofString "nb") versionedHashesBlobStep _ state post run
  rw [source_versioned_hashes_blob_step]
  rfl

#print axioms source_versioned_hashes_blob_step
#print axioms versioned_hashes_blob_step_adds_one
#print axioms versioned_hashes_blob_step_count_frame
end InitECandidate.Runtime
