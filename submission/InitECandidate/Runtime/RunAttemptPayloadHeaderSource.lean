import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.OriginalHtrPayloadCode
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual `run_attempt` statement 18 is the real `payload_header(si)` call, whose continuation
is statement 19.  This is the call site the header contract has to serve; statement 17 is the `skip`
that precedes it. -/
theorem source_run_attempt_payload_header_call : runAttemptAt 18 =
    .decCall (ofString "hdr") .one (ofString "payload_header")
      [.var .local (ofString "si")] (runAttemptAt 19) := by
  rfl

#print axioms source_run_attempt_payload_header_call

/-- Statement 17 is the `skip` in front of the actual `payload_header` call. -/
theorem source_run_attempt_payload_header_prefix : runAttemptAt 17 =
    .seq .skip (runAttemptAt 18) := by
  rfl

#print axioms source_run_attempt_payload_header_prefix

/-- The runtime's installed code really contains the whole `payload_header` function with its single
`si` parameter, i.e. the callee the call site above resolves to. -/
theorem originalRuntimeCode_payloadHeader_lookup :
    originalRuntimeCode.lookup (ofString "payload_header") =
      some ([(ofString "si",.one)],sourceFunctionBody Guest.guestFn_payload_header,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "payload_header") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "payload_header") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "payload_header")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 903 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original903 :: declarations.drop 904 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 904)).reverse).all
          (fun entry => !((ofString "payload_header") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original903 :: declarations.drop 904) =
          (ofString "payload_header",[(ofString "si",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_payload_header,ShapeHOL.one) ::
            functionsHOL (declarations.drop 904) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original903_eq]
        simp only [Guest.guestFn_payload_header,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "payload_header") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "payload_header") (functionsHOL (declarations.drop 904)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "payload_header") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_payloadHeader_lookup

end InitECandidate.Runtime
