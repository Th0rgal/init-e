import InitECandidate.Runtime.MptInsertBranchDescentSlotWorld
import InitECandidate.Runtime.MptInsertRunningChoice
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A continuing actual branch dispatch descends one key nibble while preserving
the allocated trie and preparing the real child backlink. -/
theorem mpt_insert_branch_dispatch_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level keyLength oldResult oldNode oldSlot oldLevel : BitVec 64)
 (registered : node∈branches)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word keyLength)))
 (inside : level.toNat≤keyLength.toNat) (nibbles : TrieNibbleRange s key keyLength)
 (keyExtent : key.toNat+keyLength.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertBranchDispatch=(none,post)) :
 ∃child slot,
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNibbleRange post key keyLength ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word slot)) ∧post.memory slot=.word child ∧TrieChildSlot post extensions branches slot ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word (level+1))) ∧
 level.toNat<(level+1).toNat ∧(level+1).toNat≤keyLength.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals ∧post.clock=s.clock := by
 obtain ⟨fits,descent⟩:=mpt_insert_branch_dispatch_running s post level keyLength atLevel atLength inside zero running run
 obtain ⟨output,child,slot,actual,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals,clock⟩:=
  mpt_insert_branch_descent_slot_world s live extensions branches size frontier world node key level keyLength oldResult oldNode oldSlot oldLevel 0
   registered atNode atKey atLevel fits nibbles keyExtent fullDomain atResult atNextNode atNextSlot atNextLevel zero
 have same : output=post:=(Prod.mk.inj (actual.symm.trans descent)).2
 subst output
 exact ⟨child,slot,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals,clock⟩

#print axioms mpt_insert_branch_dispatch_world
end InitECandidate.Runtime
