import InitECandidate.Runtime.MptNibbleStoredPaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete actual indexed prefix earns its fresh key path while also
retaining every stored node path and exact kind, or takes a real failure.
This is the full path-aware insertion entry, with nine source clocks. -/
theorem mpt_set_indexed_stored_paths_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (unsecured : s.memory (table+8)=.word 0) (short : length.toNat≤9)
 (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (headerExtent : table.toNat+16≤pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 Reaches s (sourceFunctionBody Guest.guestFn_mpt_set)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next (ofString "nk") pointer length ∧
   TrieNibbleRange next pointer (2*length) ∧(2*length).toNat≤18 ∧next.memory (table+8)=.word 0 ∧
   AllocatedTrieWorld next live extensions branches size (allocationEnd pointer (2*length)) ∧
   TriePathBuffer next live size pointer (2*length) (allocationEnd pointer (2*length)) ∧
   TrieNodeKinds next live extensions branches ∧
   TrieNodePaths next live extensions branches size (allocationEnd pointer (2*length))) 9 (mptSetAt 1) := by
 have reached:=mpt_set_indexed_path_prefix_reaches s table key length pointer live extensions branches size
  world atTable atKey atLength unsecured short keyBefore fullDomain headerExtent code budget
 apply reaches_mono s _ (mptSetAt 1) _ _ 9 9 (le_refl _) _ reached
 intro next facts
 obtain ⟨ready,nibbles,small,header,worldOut,currentPath⟩:=facts
 obtain ⟨kindsOut,pathsOut⟩:=ready.stored_paths live extensions branches size world kinds paths short
 exact ⟨ready,nibbles,small,header,worldOut,currentPath,kindsOut,pathsOut⟩

#print axioms mpt_set_indexed_stored_paths_prefix_reaches
end InitECandidate.Runtime
