import InitECandidate.Runtime.OriginalCreateBranchTwoLeavesCode
import InitECandidate.Runtime.OriginalSplitExtensionCode
import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.NodeNewBranchUniformBound
import InitECandidate.Runtime.OriginalNodeNewBranchCode
import InitECandidate.Runtime.NodeNewLeafUniformBound
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.NodeNewExtUniformBound
import InitECandidate.Runtime.OriginalMptFailCode
import InitECandidate.Runtime.MptFailBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem node_new_branch_fun_bounded : FunBounded (ofString "node_new_branch") 40 := by
 refine ⟨[],sourceFunctionBody Guest.guestFn_node_new_branch,.one,originalRuntimeCode_nodeNewBranch_lookup,?_⟩
 intro F s code budget
 exact runBounded_node_new_branch_body s code budget

theorem node_new_leaf_fun_bounded : FunBounded (ofString "node_new_leaf") 2 :=
 ⟨_,_,_,originalRuntimeCode_nodeNewLeaf_lookup,node_new_leaf_uniform_bounded⟩

theorem mpt_fail_fun_bounded : FunBounded (ofString "mpt_fail") 0 :=
 ⟨_,_,_,originalRuntimeCode_mptFail_lookup,
  ProgBounded.straight _ (by rw [source_mptFail_body];rfl)⟩

/-- Both actual leaf constructors and all branch stores are included, with no
input, memory-domain or successful-allocation assumptions. -/
theorem create_branch_two_leaves_body_bounded :
 ProgBounded (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves) 50 := by
 refine ProgBounded.weaken (cost:=47) ?_ (by decide)
 · rw [sourceFunctionBody_eq_structural]
   simp only [structuralFunctionBody,Guest.guestFn__create_branch_from_two_leaves,
    Guest.guestFn__split_extension,Proofs.FrontendCodecComputation.declToHOLStructural,
    Proofs.FrontendCodecComputation.funDeclToHOLStructural,Proofs.FrontendCodecComputation.progToHOLStructural]
   apply ProgBounded.decCall (tailCost:=6) node_new_branch_fun_bounded
   apply ProgBounded.seq (a:=3) (b:=3)
   · apply ProgBounded.ite
     · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
     · exact ProgBounded.decCall node_new_leaf_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
   · apply ProgBounded.seq (a:=3) (b:=0)
     · apply ProgBounded.ite
       · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
       · exact ProgBounded.decCall node_new_leaf_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
     · exact ProgBounded.straight _ rfl

/-- The complete original extension split is bounded even when source loads,
the real allocator, or the explicit mpt_fail path reject. -/
theorem split_extension_body_bounded :
 ProgBounded (sourceFunctionBody Guest.guestFn__split_extension) 50 := by
 refine ProgBounded.weaken (cost:=48) ?_ (by decide)
 · rw [sourceFunctionBody_eq_structural]
   simp only [structuralFunctionBody,Guest.guestFn__create_branch_from_two_leaves,
    Guest.guestFn__split_extension,Proofs.FrontendCodecComputation.declToHOLStructural,
    Proofs.FrontendCodecComputation.funDeclToHOLStructural,Proofs.FrontendCodecComputation.progToHOLStructural]
   apply ProgBounded.dec
   apply ProgBounded.dec
   apply ProgBounded.dec
   apply ProgBounded.decCall (tailCost:=7) node_new_branch_fun_bounded
   apply ProgBounded.dec
   apply ProgBounded.seq (a:=0) (b:=7)
   · exact ProgBounded.straight _ rfl
   · apply ProgBounded.seq (a:=3) (b:=4)
     · apply ProgBounded.ite
       · exact ProgBounded.decCall node_new_ext_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
       · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
     · apply ProgBounded.dec
       apply ProgBounded.seq (a:=4) (b:=0)
       · apply ProgBounded.ite
         · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
         · apply ProgBounded.dec
           apply ProgBounded.seq (a:=1) (b:=3)
           · apply ProgBounded.ite
             · exact ProgBounded.call mpt_fail_fun_bounded _ _
             · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
           · exact ProgBounded.decCall node_new_leaf_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
       · exact ProgBounded.straight _ rfl

theorem create_branch_two_leaves_fun_bounded :
 FunBounded (ofString "_create_branch_from_two_leaves") 50 :=
 ⟨_,_,_,originalRuntimeCode_createBranchTwoLeaves_lookup,create_branch_two_leaves_body_bounded⟩

theorem split_extension_fun_bounded : FunBounded (ofString "_split_extension") 50 :=
 ⟨_,_,_,originalRuntimeCode_splitExtension_lookup,split_extension_body_bounded⟩

#print axioms create_branch_two_leaves_fun_bounded
#print axioms split_extension_fun_bounded
#print axioms create_branch_two_leaves_body_bounded
#print axioms split_extension_body_bounded
end InitECandidate.Runtime
