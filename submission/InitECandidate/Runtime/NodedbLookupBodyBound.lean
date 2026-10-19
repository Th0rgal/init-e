import InitECandidate.Runtime.NodedbTableGetBound
import InitECandidate.Runtime.PanTwoWordResultLookup
import InitECandidate.Runtime.PanDecCallContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodedbLookupTail : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_nodedb_lookup with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

theorem source_nodedb_lookup_body : sourceFunctionBody Guest.guestFn_nodedb_lookup =
    .decCall (ofString "r") (.comb [.one,.one]) (ofString "htab_get")
      [.var .local (ofString "db"),.var .local (ofString "hash")] nodedbLookupTail := by
  unfold nodedbLookupTail sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem nodedb_lookup_tail_straight : extStraightLine nodedbLookupTail = true := by
  unfold nodedbLookupTail sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  decide

/-- The complete original node-database lookup, including value-cell loads and
the missing-key return, has a finite bound from its actual constructed table. -/
theorem runBounded_nodedb_lookup_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total key : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "hash") = some (.val (.word key)))
    (budget : nodedbGetCost + 1 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_nodedb_lookup) (nodedbGetCost + 1) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "hash")] =
      some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atTable,atKey]
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word table),.val (.word key)] =
      some (sourceFunctionBody Guest.guestFn_htab_get,callee,.comb [.one,.one]) := by
    rw [code]
    exact pan_two_word_result_lookup originalRuntimeCode.lookup (ofString "htab_get")
      (ofString "t") (ofString "key") (sourceFunctionBody Guest.guestFn_htab_get) table key
      (.comb [.one,.one]) (by decide) originalRuntimeCode_hashGet_lookup
  have entryBuilt : NodedbTableAt entry table heap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have bounded := runBounded_nodedb_table_get entry table heap total key entryBuilt
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change nodedbGetCost ≤ s.clock - 1; omega)
  unfold RunBounded at bounded
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_get) with
  | mk result post =>
    rw [bodyRun] at bounded
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_get)
    rw [bodyRun] at metadata
    rw [source_nodedb_lookup_body]
    have composed := evaluate_decCall_continuation_bounded s post (ofString "r") (ofString "htab_get")
      (.comb [.one,.one]) (.comb [.one,.one])
      [.var .local (ofString "db"),.var .local (ofString "hash")]
      [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_get) nodedbLookupTail callee
      result (nodedbGetCost + 1) 0 args lookup (by omega) bodyRun bounded.2.1
      (by have spent := bounded.1; change s.clock - 1 ≤ post.clock + nodedbGetCost at spent; omega) bounded.2.2 (by
        intro value returned
        exact RunBounded.ofProg (ProgBounded.straight _ nodedb_lookup_tail_straight)
          (metadata.1.trans code) (by omega))
    exact composed

#print axioms source_nodedb_lookup_body
#print axioms nodedb_lookup_tail_straight
#print axioms runBounded_nodedb_lookup_body
end InitECandidate.Runtime
