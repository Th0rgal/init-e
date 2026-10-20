import InitECandidate.Runtime.MptSetIndexedKeyPrefix
import InitECandidate.Runtime.TrieWalkRegistryWordFrame
import InitECandidate.Runtime.MptNibbleIndexedRangeReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual key-conversion prefix of indexed mpt_set retains its existing
unsecured header and live-node registry. Their concrete words lie below the
heap frontier, while the returned allocator and converter write at/above it. -/
theorem mpt_set_indexed_registry_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (live extensions branches : Set (BitVec 64))
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (short : length.toNat≤9)
 (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (headerExtent : table.toNat+16≤pointer.toNat)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 Reaches s (sourceFunctionBody Guest.guestFn_mpt_set)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next (ofString "nk") pointer length ∧
   (2*length).toNat≤18 ∧next.memory (table+8)=.word 0 ∧
   TrieWalkRegistry live extensions branches next) 9 (mptSetAt 1) := by
 have converted:=mpt_set_indexed_key_prefix_reaches s table key length pointer atTable atKey atLength atHeap
  unsecured short code budget
 apply reaches_mono s _ (mptSetAt 1) _ _ 9 9 (le_refl _) _ converted
 intro next facts
 have memory:=facts.1.before_memory short capped aligned
 refine ⟨facts.1,facts.2,?_,registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))⟩
 have natural : (table+8#64).toNat=table.toNat+8 := by
  rw [BitVec.toNat_add_of_lt (by change table.toNat+8<2^64;omega)]
  rfl
 rw [memory _ (by change (table+8#64).toNat<pointer.toNat;rw [natural];omega)]
 exact unsecured

#print axioms mpt_set_indexed_registry_prefix_reaches

/-- At the actual insertion/deletion dispatch, the indexed key has a valid
nibble buffer of length at most eighteen and the old traversal registry is
intact. All normal/error allocation and conversion outcomes are covered. -/
theorem mpt_set_indexed_range_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table key length pointer : BitVec 64) (live extensions branches : Set (BitVec 64))
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (unsecured : s.memory (table+8)=.word 0) (short : length.toNat≤9)
 (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (keyBefore : key.toNat+length.toNat≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (headerExtent : table.toNat+16≤pointer.toNat)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 9≤s.clock) :
 Reaches s (sourceFunctionBody Guest.guestFn_mpt_set)
  (fun next=>MptNibbleUnsecuredDeclarationReady s next (ofString "nk") pointer length ∧
   TrieNibbleRange next pointer (2*length) ∧(2*length).toNat≤18 ∧
   next.memory (table+8)=.word 0 ∧TrieWalkRegistry live extensions branches next) 9 (mptSetAt 1) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "m"),.var .local (ofString "key"),.var .local (ofString "klen")]=
  some [.val (.word table),.val (.word key),.val (.word length)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atKey,atLength]
 have converted:=mpt_nibble_indexed_range_declaration_reaches s (ofString "nk") _ (mptSetAt 1)
  table key length pointer args atHeap unsecured short capped keyBefore fullDomain code budget
 rw [←source_mpt_set_key_prefix] at converted
 apply reaches_mono s _ (mptSetAt 1) _ _ 9 9 (le_refl _) _ converted
 intro next facts
 have memory:=facts.1.before_memory short capped aligned
 refine ⟨facts.1,facts.2,?_,?_,registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))⟩
 · change (2#64*length).toNat≤18
   rw [BitVec.toNat_mul]
   change (2*length.toNat)%2^64≤18
   rw [Nat.mod_eq_of_lt (by omega)]
   omega
 · have natural : (table+8#64).toNat=table.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat+8<2^64;omega)]
    rfl
   rw [memory _ (by change (table+8#64).toNat<pointer.toNat;rw [natural];omega)]
   exact unsecured

#print axioms mpt_set_indexed_range_prefix_reaches
end InitECandidate.Runtime
