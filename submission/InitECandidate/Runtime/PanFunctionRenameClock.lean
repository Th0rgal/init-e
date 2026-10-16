import InitECandidate.Runtime.CanonicalGlobalsFunctionRelation
import InitECandidate.Runtime.PanRenameRun
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

private theorem updateList_eq_updateListEq {A B : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (map : HolFiniteMapExact A B) (entries : List (A × B)) :
    map.updateList entries = map.updateListEq entries := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList,HolFiniteMapExact.lookup_updateListEq]
  rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]

/-- Permuting a reverse-installed source function table installs the
permuted source declarations in precisely the same lookup order. -/
theorem rename_reverse_function_table {width : Nat} [NeZero width]
    (first second : MlS) (declarations : List (DeclHOL width)) :
    fpermCodeHOL first second (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse) =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL first second declarations)).reverse := by
  rw [updateList_eq_updateListEq,fpermCodeHOL_updateListEq,fpermCodeHOL_empty,
    functionsFpermDecsHOL,List.map_reverse]
  try exact (updateList_eq_updateListEq _ _).symm

noncomputable def canonicalUnrenamedSourceEntry (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  sourceEntryCode (zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames)
    (canonicalInitializedGlobals input).locals
    (HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)

theorem canonical_source_entry_rename (input : Guest.InputBlob) :
    {canonicalUnrenamedSourceEntry input with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart (canonicalUnrenamedSourceEntry input).code)} = canonicalRenamedSourceEntry input := by
  have table := rename_reverse_function_table FrontendStages.Declarations.globalStart
    FrontendStages.Declarations.globalNewStart FrontendStages.Declarations.functionDeclarations
  rw [GlobalsComputation.fpermDecs_eq_map] at table
  unfold canonicalUnrenamedSourceEntry canonicalRenamedSourceEntry
  rw [sourceEntryCode_code,sourceEntryCode_replace]
  exact congrArg (sourceEntryCode (zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames)
    (canonicalInitializedGlobals input).locals) table

/-- Swapping main and its fresh name maps the full evaluator result at the
same clock; only the post-state function table changes. -/
theorem canonical_source_entry_rename_run (input : Guest.InputBlob) (fuel : Nat)
    (result : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState {canonicalUnrenamedSourceEntry input with clock := fuel}
      (.call none FrontendStages.Declarations.globalStart []) = (result,post)) :
    evaluateHOLFiniteState {canonicalRenamedSourceEntry input with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) =
      (result,{post with code := (fpermCodeHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart post.code)}) := by
  have renamed := pan_rename_entry_run FrontendStages.Declarations.globalStart
    FrontendStages.Declarations.globalNewStart (canonicalUnrenamedSourceEntry input) fuel result post run
  have transport := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    evaluateHOLFiniteState {state with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart [])) (canonical_source_entry_rename input)
  exact transport.symm.trans renamed

#print axioms rename_reverse_function_table
#print axioms canonical_source_entry_rename
#print axioms canonical_source_entry_rename_run
end InitECandidate.Runtime
