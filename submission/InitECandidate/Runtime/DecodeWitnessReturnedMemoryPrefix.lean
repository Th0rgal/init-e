import InitECandidate.Runtime.DecodeWitnessEmptyGuard
import InitECandidate.Runtime.DecodeWitnessLookupFullContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The complete original decoder prefix either returns the empty node within
129 steps, or reaches node decoding with a readable lookup result whose byte
interval lies inside the original input. Any failed reads terminate within the
same prefix budget; query alignment is unrestricted. -/
theorem decode_witness_returned_memory_prefix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total root emptyRoot array input inputLength : BitVec 64)
    (built : NodedbTableAt s table heap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atRoot : s.locals.lookup (ofString "root_hash") = some (.val (.word root)))
    (atEmpty : s.globals.lookup (ofString "empty_trie_root") = some (.val (.word emptyRoot)))
    (code : s.code = originalRuntimeCode) (budget : 129 + (nodedbGetCost + 3) ≤ s.clock) :
    ((evaluateHOLFiniteState s (decodeWitnessAt 0)).1 = some (.returned (.val (.word (0#64)))) ∧
      RunBounded s (decodeWitnessAt 0) 129 ∧
      (evaluateHOLFiniteState s (decodeWitnessAt 0)).2.globals=s.globals ∧ (evaluateHOLFiniteState s (decodeWitnessAt 0)).2.memory=s.memory) ∨
    Reaches s (decodeWitnessAt 0)
      (fun next => ∃ found source length : BitVec 64, found ≠ 0 ∧
        next.locals.lookup (ofString "r") = some (.rStruct [.val (.word found),.val (.word source),.val (.word length)]) ∧
        next.locals.lookup (ofString "db") = some (.val (.word table)) ∧
        next.locals.lookup (ofString "root_hash") = some (.val (.word root)) ∧
        next.memory = s.memory ∧ next.globals = s.globals ∧ next.code = s.code ∧ next.memaddrs = s.memaddrs ∧ next.be = s.be ∧
        input.toNat ≤ source.toNat ∧ source.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
        source.toNat + length.toNat < 2 ^ 64 ∧ length.toNat ≤ inputLength.toNat)
      (129 + (nodedbGetCost + 3)) (decodeWitnessAt 4) := by
  have first := decode_witness_root_comparison_bounded_reaches s root emptyRoot atRoot atEmpty code (by omega)
  rcases first with ⟨ready,⟨word,locals,memory,globals,installed,domain,endian⟩,spent,remaining,scopeEq⟩ | abort
  · have atWord : ready.locals.lookup (ofString "is_empty") = some (.val (.word word)) := by
      rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    by_cases empty : word = 0
    · have guardRun := evaluate_decode_witness_empty_guard ready word atWord
      rw [if_pos empty] at guardRun
      have reachedPrefix : Reaches s (decodeWitnessAt 0) (fun mid => mid = ready) 129 (decodeWitnessAt 2) := by
        exact Or.inl ⟨ready,rfl,spent,remaining,by rw [guardRun] at scopeEq; exact scopeEq⟩
      right
      refine reaches_trans_budget s (decodeWitnessAt 0) (decodeWitnessAt 2) (decodeWitnessAt 4)
        _ _ 129 (nodedbGetCost + 3) budget reachedPrefix ?_
      intro mid same ticks
      subst mid
      have readyBuilt : NodedbTableAt ready table heap total := by
        obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
        exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.congr domain endian installed
          (by intro off ho; exact congrFun memory _) (by intro address inside; exact congrFun memory _),
          ordered.transfer memory domain endian,extent⟩
      have readySlices : RlpSliceInputPrefix ready array input inputLength total.toNat := by
        intro index inside
        obtain ⟨pointer,length,slice⟩ := slices index inside
        exact ⟨pointer,length,slice.after_frame s ready array index pointer length input inputLength domain
          (congrFun memory _) (congrFun memory _)⟩
      have tableLocal : ready.locals.lookup (ofString "db") = some (.val (.word table)) := by
        rw [locals]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,atTable]
      have rootLocal : ready.locals.lookup (ofString "root_hash") = some (.val (.word root)) := by
        rw [locals]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,atRoot]
      have lookup := decode_witness_lookup_full_context_reaches ready table heap total root array input inputLength
        readyBuilt (entries.after_read memory domain endian) readySlices (installed.trans code) tableLocal rootLocal ticks
      apply reaches_mono ready _ (decodeWitnessAt 4) _ _ _ _ (Nat.le_refl _) ?_ lookup
      intro next facts
      obtain ⟨found,source,length,nonzero,localNext,memNext,globalNext,codeNext,domNext,beNext,lo,hi,nowrap,bound⟩ := facts
      refine ⟨found,source,length,nonzero,?_,?_,?_,memNext.trans memory,globalNext.trans globals,codeNext.trans installed,
        domNext.trans domain,beNext.trans endian,lo,hi,nowrap,bound⟩
      · rw [localNext]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      · rw [localNext]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,tableLocal]
      · rw [localNext]; simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,rootLocal]
    · have guardRun := evaluate_decode_witness_empty_guard ready word atWord
      rw [if_neg empty] at guardRun
      rw [guardRun] at scopeEq
      left
      refine ⟨scopeEq.1,⟨?_,?_,?_⟩,?_,?_⟩
      · rw [scopeEq.2.1]; exact spent
      · rw [scopeEq.2.1]; exact remaining
      · rw [scopeEq.1]; simp
      · exact scopeEq.2.2.2.1.trans globals
      · exact scopeEq.2.2.1.trans memory
  · right
    exact Or.inr (stAbort_mono s _ 129 (129 + (nodedbGetCost + 3)) (by omega) abort)

#print axioms decode_witness_returned_memory_prefix
end InitECandidate.Runtime
