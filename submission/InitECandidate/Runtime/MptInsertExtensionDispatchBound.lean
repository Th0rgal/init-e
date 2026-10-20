import InitECandidate.Runtime.MptInsertExtensionComparison
import InitECandidate.Runtime.MptInsertBranchConstructorsBound
import InitECandidate.Runtime.CommonPrefixUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertExtensionDispatch : ProgHOL 64 :=
 match mptInsertKindDispatch with | .seq _ (.seq _ (.ite _ _ (.ite _ branch _)))=>branch | _=>.skip

theorem source_mptInsert_extension_dispatch : mptInsertExtensionDispatch=
 .dec (ofString "seg") .one (.load .one (mptInsertNodeAddress 32))
  (.dec (ofString "sl") .one (.load .one (mptInsertNodeAddress 40)) mptInsertExtensionComparison) := by
 simp only [mptInsertExtensionDispatch,mptInsertExtensionComparison,mptInsertKindDispatch,mptInsertLoopStep,
  sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem mpt_insert_extension_split_bounded : ProgBounded mptInsertExtensionSplit 54 := by
 simp only [mptInsertExtensionSplit,mptInsertExtensionContinuation,mptInsertExtensionComparison,
  mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
 apply ProgBounded.decCall (tailCost:=3) split_extension_fun_bounded
 apply ProgBounded.ite
 · exact ProgBounded.call node_new_ext_fun_bounded _ _
 · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)

theorem mpt_insert_extension_continuation_bounded : ProgBounded mptInsertExtensionContinuation 54 := by
 rw [source_mptInsert_extension_continuation]
 apply ProgBounded.ite
 · have fast : ProgBounded mptInsertExtensionAdvance 0 := by
    rw [source_mptInsert_extension_advance]
    exact ProgBounded.straight _ rfl
   intro F s code budget
   obtain ⟨spent,remaining,safe⟩:=fast s code (by omega)
   exact ⟨by omega,remaining,safe⟩
 · exact mpt_insert_extension_split_bounded

/-- The actual entire extension branch, including the real comparison loop,
matched-path assignments, split constructor and optional new extension, is
bounded for all input shapes, invalid memory and allocator rejections. -/
theorem mpt_insert_extension_dispatch_bounded : ProgBounded mptInsertExtensionDispatch (2^64+60) := by
 have comparison : ProgBounded mptInsertExtensionComparison ((1+2^64)+1+54) := by
  rw [source_mptInsert_extension_comparison]
  exact ProgBounded.decCall common_prefix_fun_bounded _ _ _ mpt_insert_extension_continuation_bounded
 have whole : ProgBounded mptInsertExtensionDispatch ((1+2^64)+1+54) := by
  rw [source_mptInsert_extension_dispatch]
  apply ProgBounded.dec
  apply ProgBounded.dec
  intro F s code budget
  exact comparison s code budget
 intro F s code budget
 obtain ⟨spent,remaining,safe⟩:=whole s code (by omega)
 exact ⟨by omega,remaining,safe⟩

#print axioms mpt_insert_extension_split_bounded
#print axioms mpt_insert_extension_continuation_bounded
#print axioms mpt_insert_extension_dispatch_bounded
end InitECandidate.Runtime
