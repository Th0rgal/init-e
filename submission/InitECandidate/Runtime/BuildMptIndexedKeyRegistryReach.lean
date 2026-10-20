import InitECandidate.Runtime.BuildMptIndexedKeyReach
import InitECandidate.Runtime.TrieWalkRegistryWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual index-key encoding keeps an unsecured trie header and every
live-node traversal fact when those owned words follow the global key buffer.
Its output length is derived from the original writer, rather than assumed
by the later insertion call. -/
theorem build_mpt_indexed_key_registry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer index table : BitVec 64) (DF : Nat) (live extensions branches : Set (BitVec 64))
 (atScratch : s.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word pointer)))
 (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (headerAfter : pointer.toNat+9≤table.toNat) (headerExtent : table.toNat+16≤2^64)
 (unsecured : s.memory (table+8)=.word 0)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedAfter : ∀address,TrieWalkRegistryWord live extensions branches address→pointer.toNat+9≤address.toNat)
 (budget : rlpWriterSourceCost+1≤s.clock) :
 Reaches s buildMptIndexedLoopBody
  (fun next=>RlpWordDeclarationReady s next (ofString "klen") pointer DF ∧
   next.memory (table+8)=.word 0 ∧TrieWalkRegistry live extensions branches next)
  (rlpWriterSourceCost+1) buildMptIndexedKeyTail := by
 have encoded:=build_mpt_indexed_key_reaches s pointer index DF atScratch atIndex code fence cap lower upper budget
 apply reaches_mono s buildMptIndexedLoopBody buildMptIndexedKeyTail _ _ _ _ (le_refl _) _ encoded
 intro next ready
 have memory:=ready.choose_spec.2.2.2.2.2.2.2.2.2
 refine ⟨ready,?_,registry.after_word_frame (fun address owned=>memory address (ownedAfter address owned))⟩
 have natural : (table+8#64).toNat=table.toNat+8 := by
  rw [BitVec.toNat_add_of_lt (by change table.toNat+8<2^64;omega)]
  rfl
 rw [memory _ (by change pointer.toNat+9≤(table+8#64).toNat;rw [natural];omega)]
 exact unsecured

#print axioms build_mpt_indexed_key_registry_reaches
end InitECandidate.Runtime
