import InitECandidate.Runtime.PanBulkExpressionCost
import Guest.Ast
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

mutual
  /-- Inspect every source load, including loads inside named fields and call
  arguments. This is a load-site certificate, not a runtime/gas bound. -/
  def bulkLoadSitesExp : ExpHOL 64 → Bool
    | .load shape address => decide (sizeOfShapeHOL shape ≤ 6) &&
        scalarLowering address && isWfShapeExactHOL ([] : StructContextExact) shape && bulkLoadSitesExp address
    | .rstruct es | .op _ es | .panop _ es => bulkLoadSitesExps es
    | .nstruct _ fields => bulkLoadSitesFields fields
    | .rfield _ e | .nfield _ e | .load32 e | .loadByte e => bulkLoadSitesExp e
    | .cmp _ a b | .shift _ a b => bulkLoadSitesExp a && bulkLoadSitesExp b
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def bulkLoadSitesExps : List (ExpHOL 64) → Bool
    | [] => true
    | e :: es => bulkLoadSitesExp e && bulkLoadSitesExps es
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def bulkLoadSitesFields : List (MlStringHOL × ExpHOL 64) → Bool
    | [] => true
    | (_, e) :: fields => bulkLoadSitesExp e && bulkLoadSitesFields fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

def bulkLoadSitesProg : ProgHOL 64 → Bool
  | .dec _ _ e body => bulkLoadSitesExp e && bulkLoadSitesProg body
  | .assign _ _ e | .return e | .raise _ e => bulkLoadSitesExp e
  | .primitive _ _ es => bulkLoadSitesExps es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => bulkLoadSitesExp a && bulkLoadSitesExp b
  | .seq a b => bulkLoadSitesProg a && bulkLoadSitesProg b
  | .ite e a b => bulkLoadSitesExp e && bulkLoadSitesProg a && bulkLoadSitesProg b
  | .while e body => bulkLoadSitesExp e && bulkLoadSitesProg body
  | .call (some (_, some (_, _, handler))) _ es => bulkLoadSitesExps es && bulkLoadSitesProg handler
  | .call _ _ es => bulkLoadSitesExps es
  | .decCall _ _ _ es body => bulkLoadSitesExps es && bulkLoadSitesProg body
  | .extCall _ a b c d => bulkLoadSitesExp a && bulkLoadSitesExp b && bulkLoadSitesExp c && bulkLoadSitesExp d
  | .shMemLoad _ _ _ e => bulkLoadSitesExp e
  | _ => true
termination_by p => sizeOf p

def bulkLoadSitesDecl : Decl (BitVec 64) → Bool
  | .function function => bulkLoadSitesProg (progToHOL function.body)
  | .decl _ _ value => bulkLoadSitesExp (expToHOL value)
  | _ => true

/-- Kernel-checked applicability of the bounded load-site pattern to the
pinned guest AST. This does not establish compiled-artifact agreement or cost. -/
theorem guest_bulk_load_sites : Guest.guestAst.all bulkLoadSitesDecl = true := by
  decide_cbv

#print axioms guest_bulk_load_sites
end InitECandidate.Runtime.FineCost
