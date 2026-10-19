import InitECandidate.Runtime.ResolveStepReturnedTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned source/database slices come from the actual database lookup and
concrete slice registry. Hash references may jump to a different input subspan. -/
theorem resolve_step_lookup_returned_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table heap total array kind key payload consumed input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s resolveStepLookup = (some (.returned value),post)) :
    ResolveStepResultSpan input inputLength value := by
  let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "it"))] =
      some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atItem]
  have lookup := lookup_nodedb_lookup_callee table key
  rw [← code] at lookup
  rw [source_resolve_step_lookup] at run
  obtain ⟨result,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "r") (ofString "nodedb_lookup")
      (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_nodedb_lookup) resolveStepLookupTail (nodedbLookupCallee table key)
      value args lookup run
  have entryBuilt : NodedbTableAt entry table heap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have entrySlices : RlpSliceInputPrefix entry array input inputLength total.toNat := by
    intro index inside
    obtain ⟨p,n,slice⟩ := slices index inside
    exact ⟨p,n,slice.after_frame s entry array index p n input inputLength rfl rfl rfl⟩
  have resultSpan := nodedb_lookup_returned_slice entry bodyPost table heap total key array input inputLength
    entryBuilt (entries.after_read rfl rfl rfl) entrySlices code
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE]) result bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_lookup)
  rw [bodyRun] at metadata
  exact resolve_step_lookup_tail_returned_result
    (setVarHOLFinite (ofString "r") result {bodyPost with locals := s.locals}) output
    kind key payload consumed input inputLength result value
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "r" ≠ ofString "it" by decide] using atItem)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) resultSpan
    (metadata.1.trans code) tailRun

#print axioms resolve_step_lookup_returned_result
end InitECandidate.Runtime
