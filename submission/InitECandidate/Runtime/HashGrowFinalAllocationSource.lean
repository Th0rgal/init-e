import InitECandidate.Runtime.HashGrowFinalAllocation32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Locate a literal declaration-call scope without replacing its body. -/
def sourceFindDeclarationCallScope (name : MlS) : ProgHOL 64 → Option (ProgHOL 64)
  | .decCall binder shape callee args body =>
      if binder == name then some (.decCall binder shape callee args body) else sourceFindDeclarationCallScope name body
  | .dec _ _ _ body => sourceFindDeclarationCallScope name body
  | .seq first rest => (sourceFindDeclarationCallScope name first).orElse (fun _ => sourceFindDeclarationCallScope name rest)
  | _ => none

/-- The checked final allocation/initialization composition is the literal
norder_pos declaration-call scope of the original growth source. -/
theorem source_htabGrow_final_allocation :
    sourceFindDeclarationCallScope (ofString "norder_pos") (sourceFunctionBody Guest.guestFn_htab_grow) =
      some (.decCall (ofString "norder_pos") .one (ofString "alloc")
        [.panop .mul [.var .local (ofString "ncap"),.const 8]]
        (hashGrowZeroHeader (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0)))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_htabGrow_final_allocation
end InitECandidate.Runtime
