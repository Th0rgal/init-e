import InitECandidate.Runtime.DecodeWitnessRootComparison
import InitECandidate.Runtime.NodedbLookupBodyBound
import InitECandidate.Runtime.OriginalNodedbLookupCode
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodedbLookupCallee (table key : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "db",.val (.word table))).update (ofString "hash",.val (.word key))

theorem lookup_nodedb_lookup_callee (table key : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "nodedb_lookup")
      [.val (.word table),.val (.word key)] =
      some (sourceFunctionBody Guest.guestFn_nodedb_lookup,nodedbLookupCallee table key,.comb [.one,.one,.one]) := by
  exact pan_two_word_result_lookup originalRuntimeCode.lookup (ofString "nodedb_lookup")
    (ofString "db") (ofString "hash") (sourceFunctionBody Guest.guestFn_nodedb_lookup)
    table key (.comb [.one,.one,.one]) (by decide) originalRuntimeCode_nodedbLookup_lookup

theorem source_decode_witness_lookup : decodeWitnessAt 2 =
    .decCall (ofString "r") (.comb [.one,.one,.one]) (ofString "nodedb_lookup")
      [.var .local (ofString "db"),.var .local (ofString "root_hash")] (decodeWitnessAt 3) := by
  unfold decodeWitnessAt sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual witness-decoder lookup either terminates in the proved budget or
reaches its real continuation with its checked return and exact caller state. -/
theorem decode_witness_lookup_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total key : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "root_hash") = some (.val (.word key)))
    (budget : nodedbGetCost + 2 ≤ s.clock) :
    Reaches s (decodeWitnessAt 2)
      (fun ready => ∃ value : ValueHOL 64, ∃ post : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (nodedbLookupCallee table key))
          (sourceFunctionBody Guest.guestFn_nodedb_lookup) = (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one]) = true ∧
        ready = setVarHOLFinite (ofString "r") value {post with locals := s.locals})
      (nodedbGetCost + 2) (decodeWitnessAt 3) := by
  let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "root_hash")] =
      some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atTable,atKey]
  have entryBuilt : NodedbTableAt entry table heap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have bounded := runBounded_nodedb_lookup_body entry table heap total key entryBuilt code
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change nodedbGetCost + 1 ≤ s.clock - 1; omega)
  rw [source_decode_witness_lookup]
  apply bounded_decCall_reaches s (ofString "r") (ofString "nodedb_lookup") (.comb [.one,.one,.one])
    (.comb [.one,.one,.one]) [.var .local (ofString "db"),.var .local (ofString "root_hash")]
    [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_nodedb_lookup)
    (decodeWitnessAt 3) (nodedbLookupCallee table key) (nodedbGetCost + 1) _ args
    (by rw [code]; exact lookup_nodedb_lookup_callee table key) (by omega) bounded
  intro value post run checked
  exact ⟨value,post,run,checked.1,rfl⟩

#print axioms lookup_nodedb_lookup_callee
#print axioms source_decode_witness_lookup
#print axioms decode_witness_lookup_reaches
end InitECandidate.Runtime
