import InitECandidate.Runtime.ResolveStepSource
import InitECandidate.Runtime.NodeNewHashedUniformBound
import InitECandidate.Runtime.DecodeWitnessLookupReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resolve_step_hashed_uniform_bounded : ProgBounded resolveStepHashed 3 := by
  rw [source_resolve_step_hashed]
  exact ProgBounded.decCall node_new_hashed_fun_bounded (ofString "hn") .one _
    (ProgBounded.straight _ rfl)

theorem resolve_step_lookup_tail_uniform_bounded : ProgBounded resolveStepLookupTail 3 := by
  rw [source_resolve_step_lookup_tail]
  exact ProgBounded.seq
    (ProgBounded.ite _ resolve_step_hashed_uniform_bounded
      (ProgBounded.weaken (ProgBounded.straight .skip rfl) (by omega)))
    (ProgBounded.straight _ rfl)

/-- The actual database declaration reaches its real tail carrying the actual
checked returned body execution, rather than an assumed lookup result. -/
theorem resolve_step_lookup_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total kind key payload consumed : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (budget : nodedbGetCost + 2 ≤ s.clock) :
    Reaches s resolveStepLookup
      (fun ready => ∃ value : ValueHOL 64, ∃ post : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (nodedbLookupCallee table key))
          (sourceFunctionBody Guest.guestFn_nodedb_lookup) = (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one]) = true ∧
        ready = setVarHOLFinite (ofString "r") value {post with locals := s.locals})
      (nodedbGetCost + 2) resolveStepLookupTail := by
  let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "it"))] =
      some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atItem]
  have entryBuilt : NodedbTableAt entry table heap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have bounded := runBounded_nodedb_lookup_body entry table heap total key entryBuilt code
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change nodedbGetCost + 1 ≤ s.clock - 1; omega)
  rw [source_resolve_step_lookup]
  apply bounded_decCall_reaches s (ofString "r") (ofString "nodedb_lookup") (.comb [.one,.one,.one])
    (.comb [.one,.one,.one]) _ [.val (.word table),.val (.word key)]
    (sourceFunctionBody Guest.guestFn_nodedb_lookup) resolveStepLookupTail (nodedbLookupCallee table key)
    (nodedbGetCost + 1) _ args (by rw [code]; exact lookup_nodedb_lookup_callee table key) (by omega) bounded
  intro value post run checked
  exact ⟨value,post,run,checked.1,rfl⟩

theorem runBounded_resolve_step_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total kind key payload consumed : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (budget : nodedbGetCost + 5 ≤ s.clock) :
    RunBounded s resolveStepLookup (nodedbGetCost + 5) := by
  have reached := resolve_step_lookup_reaches s table heap total kind key payload consumed built code atTable atItem (by omega)
  have result := RunBounded.ofReaches (tailCost := 3) (by omega : nodedbGetCost+2+3 ≤ s.clock) reached (by
    intro ready facts ticks
    obtain ⟨value,post,run,checked,same⟩ := facts
    have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s (nodedbLookupCallee table key))
      (sourceFunctionBody Guest.guestFn_nodedb_lookup)
    rw [run] at metadata
    exact RunBounded.ofProg resolve_step_lookup_tail_uniform_bounded (by rw [same]; exact metadata.1.trans code) ticks)
  exact result

#print axioms resolve_step_hashed_uniform_bounded
#print axioms resolve_step_lookup_tail_uniform_bounded
#print axioms resolve_step_lookup_reaches
#print axioms runBounded_resolve_step_lookup
end InitECandidate.Runtime
