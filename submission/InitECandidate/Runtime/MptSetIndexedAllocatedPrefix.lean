import InitECandidate.Runtime.MptSetIndexedRegistryPrefix
import InitECandidate.Runtime.AllocatedTrieWorld
import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual indexed key allocation advances the heap frontier while preserving
all previously allocated trie records and positive extension lengths. -/
theorem MptNibbleUnsecuredDeclarationReady.allocated_world {F : Type}
 {s next : PanSemStateFiniteExact 64 F} {name : MlS} {pointer length : BitVec 64}
 (ready : MptNibbleUnsecuredDeclarationReady s next name pointer length)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer) (short : length.toNat≤9) :
 AllocatedTrieWorld next live extensions branches size (allocationEnd pointer (2*length)) := by
 have before:=ready.before_memory short world.capped world.aligned
 rcases ready with ⟨atKey,locals,globals,request,capped,domain,endian,code,_⟩
 have sum:=allocationGuard_sum_bound pointer (2*length) world.capped request
 obtain ⟨cover,_,aligned⟩:=allocationEnd_covers pointer (2*length) sum
 have words : ∀address,TrieWalkRegistryWord live extensions branches address→next.memory address=s.memory address:=
  fun address owned=>before address (world.owned_below address owned)
 refine ⟨world.registry.after_word_frame words,world.positive.after_registry_word_frame words,world.layout,?_,?_,capped,aligned⟩
 · intro node member
   have bound:=world.allocated node member
   omega
 · rw [globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

/-- The full original indexed mpt_set prefix reaches insertion dispatch with
its concrete allocated trie world, a valid fresh nibble key, and actual new
heap frontier, or terminates through a real source failure. -/
theorem mpt_set_indexed_allocated_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
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
   AllocatedTrieWorld next live extensions branches size (allocationEnd pointer (2*length))) 9 (mptSetAt 1) := by
 have reached:=mpt_set_indexed_range_prefix_reaches s table key length pointer live extensions branches
  atTable atKey atLength world.heap unsecured short world.capped world.aligned keyBefore fullDomain headerExtent world.registry world.owned_below code budget
 apply reaches_mono s _ (mptSetAt 1) _ _ 9 9 (le_refl _) _ reached
 intro next facts
 exact ⟨facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.1.allocated_world live extensions branches size world short⟩

#print axioms MptNibbleUnsecuredDeclarationReady.allocated_world
#print axioms mpt_set_indexed_allocated_prefix_reaches
end InitECandidate.Runtime
