import InitECandidate.Runtime.DecodeWitnessLookupGuard
import InitECandidate.Runtime.ThreeWordValueShape
import InitECandidate.Runtime.MemKeepProgram
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual lookup and missing-key guard reach node decoding with typed
result words and a nonzero flag, keeping caller memory in every normal case. -/
theorem decode_witness_lookup_to_node_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total key : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "root_hash") = some (.val (.word key)))
    (budget : nodedbGetCost + 3 ≤ s.clock) :
    Reaches s (decodeWitnessAt 2)
      (fun next => ∃ found source length : BitVec 64, found ≠ 0 ∧
        next.locals = s.locals.update (ofString "r",
          .rStruct [.val (.word found),.val (.word source),.val (.word length)]) ∧
        next.memory = s.memory ∧ next.code = s.code ∧ next.memaddrs = s.memaddrs ∧ next.be = s.be)
      (nodedbGetCost + 3) (decodeWitnessAt 4) := by
  have first := decode_witness_lookup_reaches s table heap total key built code atTable atKey (by omega)
  refine reaches_trans_budget s (decodeWitnessAt 2) (decodeWitnessAt 3) (decodeWitnessAt 4)
    _ _ (nodedbGetCost + 2) 1 (by omega) first (by
      intro ready facts ticks
      obtain ⟨value,post,run,checked,same⟩ := facts
      obtain ⟨found,source,length,valueEq⟩ := value_three_words_of_checked_shape value checked
      subst value
      let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
      have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_lookup)
      rw [run] at metadata
      have memory := evaluate_keeps_mem (sourceFunctionBody Guest.guestFn_nodedb_lookup)
        (keepsMem_of_installed originalRuntimeCode_nodedbLookup_lookup (by decide_cbv)) entry code
      rw [run] at memory
      have atResult : ready.locals.lookup (ofString "r") =
          some (.rStruct [.val (.word found),.val (.word source),.val (.word length)]) := by
        rw [same]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have readyCode : ready.code = originalRuntimeCode := by
        rw [same]
        exact metadata.1.trans code
      have guard := decode_witness_lookup_guard_reaches ready found source length atResult readyCode (by omega)
      apply reaches_mono ready (decodeWitnessAt 3) (decodeWitnessAt 4) _ _ _ _ (Nat.le_refl _) _ guard
      intro next guardFacts
      obtain ⟨nonzero,rfl⟩ := guardFacts
      refine ⟨found,source,length,nonzero,?_,?_,?_,?_,?_⟩
      · rw [same]; rfl
      · rw [same]; exact memory
      · rw [same]; exact metadata.1
      · rw [same]; exact metadata.2.1
      · rw [same]; exact metadata.2.2.1)

#print axioms decode_witness_lookup_to_node_reaches
end InitECandidate.Runtime
