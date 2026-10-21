import ActualCandidateCodePrefix
import ActualCandidateCodeNames
import InitECandidate.Runtime.OriginalRuntimeCode

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

/-- Code map of the frozen full-guest candidate AST. -/
def candidateRuntimeCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  HolFiniteMapExact.empty.updateList
    (functionsHOL (CandidateGuest.guestAst.map declToHOL))

/-- `scratch_alloc` is installed with the shared body in the frozen full-guest
candidate code. -/
theorem candidate_scratchAllocation_lookup :
    candidateRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],
        sourceFunctionBody CandidateGuest.guestFn_scratch_alloc,.one) := by
  change (HolFiniteMapExact.empty.updateList
    (functionsHOL (CandidateGuest.guestAst.map declToHOL))).lookup _ = _
  calc
    _ = List.lookup (ofString "scratch_alloc")
        (functionsHOL (CandidateGuest.guestAst.map declToHOL)).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL (CandidateGuest.guestAst.map declToHOL))
        (ofString "scratch_alloc") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup
          (functionsHOL (CandidateGuest.guestAst.map declToHOL)).reverse
          (ofString "scratch_alloc")
    _ = _ := by
      let declarations := CandidateGuest.guestAst
      have split : declarations = declarations.take 13 ++
          CandidateGuest.guestFn_scratch_alloc :: declarations.drop 14 := by kernel_rfl
      let before := (declarations.take 13).map declToHOL
      let after := (declarations.drop 14).map declToHOL
      have mapSplit : declarations.map declToHOL =
          before ++ declToHOL CandidateGuest.guestFn_scratch_alloc :: after := by
        rw [split, List.map_append, List.map_cons]
      have absent : (functionsHOL after).all
          (fun entry => !((ofString "scratch_alloc") == entry.1)) = true := by
        rw [functionsHOL_all]
        change (declaredFunctionNames (declarations.drop 14)).all
          (fun name => !((ofString "scratch_alloc") == name)) = true
        decide
      have absentRev : ((functionsHOL after).reverse).all
          (fun entry => !((ofString "scratch_alloc") == entry.1)) = true := by
        rw [List.all_reverse]
        exact absent
      have head : functionsHOL (declToHOL CandidateGuest.guestFn_scratch_alloc :: after) =
          (ofString "scratch_alloc",[(ofString "n",ShapeHOL.one)],
            sourceFunctionBody CandidateGuest.guestFn_scratch_alloc,ShapeHOL.one) ::
            functionsHOL after := by
        simp [CandidateGuest.guestFn_scratch_alloc, declToHOL, functionsHOL,
          funDeclToHOL, sourceFunctionBody, paramToHOL, shapeToHOL]
      rw [show CandidateGuest.guestAst = declarations from rfl]
      rw [mapSplit, functionsHOL_append, head, List.reverse_append, List.reverse_cons,
        List.append_assoc]
      rw [lookup_skip_prefix_generic _ _ _ absentRev]
      simp only [List.singleton_append, List.lookup_cons, beq_self_eq_true]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_scratchAllocation_lookup
