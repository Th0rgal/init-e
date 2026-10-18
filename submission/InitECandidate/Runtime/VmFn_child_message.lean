import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_msg_new_scratch

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_child_message :
    originalRuntimeCode.lookup (ofString "child_message") =
      some ([(ofString "caller",.one),(ofString "target",.one),(ofString "current_target",.one),(ofString "gas",.one),(ofString "reservoir",.one),(ofString "value",.comb [.one,.one,.one,.one]),(ofString "data",.one),(ofString "data_n",.one),(ofString "code_address",.one),(ofString "code",.one),(ofString "code_n",.one),(ofString "transfer",.one),(ofString "is_static",.one),(ofString "disable_pre",.one)],sourceFunctionBody Guest.guestFn_child_message,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "child_message") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "child_message") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "child_message")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 597 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original597 :: declarations.drop 598 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 598)).reverse).all
          (fun entry => !((ofString "child_message") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original597 :: declarations.drop 598) =
          (ofString "child_message",[(ofString "caller",ShapeHOL.one),(ofString "target",ShapeHOL.one),(ofString "current_target",ShapeHOL.one),(ofString "gas",ShapeHOL.one),(ofString "reservoir",ShapeHOL.one),(ofString "value",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "data",ShapeHOL.one),(ofString "data_n",ShapeHOL.one),(ofString "code_address",ShapeHOL.one),(ofString "code",ShapeHOL.one),(ofString "code_n",ShapeHOL.one),(ofString "transfer",ShapeHOL.one),(ofString "is_static",ShapeHOL.one),(ofString "disable_pre",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_child_message,ShapeHOL.one) ::
            functionsHOL (declarations.drop 598) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original597_eq]
        simp only [Guest.guestFn_child_message,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "child_message") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "child_message") (functionsHOL (declarations.drop 598)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "child_message") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_child_message

theorem vmBound_child_message : FunBounded (ofString "child_message") 42 :=
  ⟨_,_,_,vmLookup_child_message,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_msg_new_scratch]
    · decide⟩

#print axioms vmBound_child_message
end InitECandidate.Runtime
