import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_trieWalk_lookup :
    originalRuntimeCode.lookup (ofString "trie_walk") =
      some ([(ofString "node",.one),(ofString "nibs",.one),(ofString "nlen",.one)],sourceFunctionBody Guest.guestFn_trie_walk,.comb [.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "trie_walk") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "trie_walk") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "trie_walk")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 269 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original269 :: declarations.drop 270 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 270)).reverse).all
          (fun entry => !((ofString "trie_walk") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original269 :: declarations.drop 270) =
          (ofString "trie_walk",[(ofString "node",ShapeHOL.one),(ofString "nibs",ShapeHOL.one),(ofString "nlen",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_trie_walk,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 270) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original269_eq]
        simp only [Guest.guestFn_trie_walk,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "trie_walk") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "trie_walk") (functionsHOL (declarations.drop 270)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "trie_walk") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_trieWalk_lookup

end InitECandidate.Runtime
