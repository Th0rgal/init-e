import InitECandidate.Runtime.DecodeWitnessLookupGuard
import InitECandidate.Runtime.NodedbLookupReturnedSlice
import InitECandidate.Runtime.ThreeWordValueShape
import InitECandidate.Runtime.NodedbLookupMemoryFrame
import InitECandidate.Runtime.MemKeepProgram
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual lookup and guard reach node decoding with a source/length pair
inside the original input, derived from the real returned database value. -/
theorem decode_witness_lookup_full_context_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total key array input inputLength : BitVec 64) (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "root_hash") = some (.val (.word key)))
    (budget : nodedbGetCost + 3 ≤ s.clock) :
    Reaches s (decodeWitnessAt 2)
      (fun next => ∃ found source length : BitVec 64, found ≠ 0 ∧
        next.locals = s.locals.update (ofString "r",
          .rStruct [.val (.word found),.val (.word source),.val (.word length)]) ∧
        next.memory = s.memory ∧ next.globals = s.globals ∧ next.code = s.code ∧ next.memaddrs = s.memaddrs ∧ next.be = s.be ∧
        input.toNat ≤ source.toNat ∧ source.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
        source.toNat + length.toNat < 2 ^ 64 ∧ length.toNat ≤ inputLength.toNat)
      (nodedbGetCost + 3) (decodeWitnessAt 4) := by
  have first := decode_witness_lookup_reaches s table heap total key built code atTable atKey (by omega)
  refine reaches_trans_budget s (decodeWitnessAt 2) (decodeWitnessAt 3) (decodeWitnessAt 4)
    _ _ (nodedbGetCost + 2) 1 (by omega) first (by
      intro ready facts ticks
      obtain ⟨value,post,run,checked,same⟩ := facts
      obtain ⟨found,source,length,valueEq⟩ := value_three_words_of_checked_shape value checked
      subst value
      let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
      have entryBuilt : NodedbTableAt entry table heap total := by
        obtain ⟨k,sd,c,u,val,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
        exact ⟨k,sd,c,u,val,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
      have entrySlices : RlpSliceInputPrefix entry array input inputLength total.toNat := by
        intro index inside
        obtain ⟨pointer,size,slice⟩ := slices index inside
        exact ⟨pointer,size,slice.after_frame s entry array index pointer size input inputLength rfl rfl rfl⟩
      have resultSpan := nodedb_lookup_returned_slice entry post table heap total key array input inputLength
        entryBuilt (entries.after_read rfl rfl rfl) entrySlices code
        (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE])
        (by simp [entry,callEntryStateHOLFinite,nodedbLookupCallee,HolFiniteMapExact.lookup_update,FUPDATE]) _ run
      have globalFrame := nodedb_lookup_memoryFrame entry code
      rw [run] at globalFrame
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
      refine ⟨found,source,length,nonzero,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [same]; rfl
      · rw [same]; exact memory
      · rw [same]; exact globalFrame.2
      · rw [same]; exact metadata.1
      · rw [same]; exact metadata.2.1
      · rw [same]; exact metadata.2.2.1
      · rcases resultSpan with missing | ⟨pointer,size,returned,lo,hi,nowrap,bound⟩
        · simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at missing
          exact False.elim (nonzero missing.1)
        · simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at returned
          obtain ⟨_,sourceEq,lengthEq,_⟩ := returned
          subst sourceEq lengthEq
          exact ⟨lo,hi,nowrap,bound⟩)

#print axioms decode_witness_lookup_full_context_reaches
end InitECandidate.Runtime
