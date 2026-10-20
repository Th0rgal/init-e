import InitECandidate.Runtime.MptInsertBranchDescentBacklink
import InitECandidate.Runtime.AllocatedTrieMetadata
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Real allocated node extents and the indexed key extent earn both the
nibble read and all sixteen child-slot domains used by the original descent.
The resulting backlink contains the selected child, and the whole concrete
trie world and key range survive the actual source execution. -/
theorem mpt_insert_branch_descent_slot_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level keyLength oldResult oldNode oldSlot oldLevel oldGo : BitVec 64)
 (registered : node∈branches)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (fits : level.toNat<keyLength.toNat) (nibbles : TrieNibbleRange s key keyLength)
 (keyExtent : key.toNat+keyLength.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (atGo : s.locals.lookup (ofString "go")=some (.val (.word oldGo))) :
 ∃post child slot,evaluateHOLFiniteState s mptInsertBranchDescent=(none,post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNibbleRange post key keyLength ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word slot)) ∧post.memory slot=.word child ∧TrieChildSlot post extensions branches slot ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word (level+1))) ∧
 level.toNat<(level+1).toNat ∧(level+1).toNat≤keyLength.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals ∧post.clock=s.clock := by
 have keyAdd : (key+level).toNat=key.toNat+level.toNat:=BitVec.toNat_add_of_lt (by omega)
 have keyDomain : s.memaddrs (panByteAlignHOL (key+level)) := by
  apply fullDomain
  rw [panByteAlign_toNat64,keyAdd]
  have:=Nat.div_mul_le_self (key.toNat+level.toNat) 8
  omega
 have childDomains : ∀slot : Nat,slot<16→s.memaddrs (branchChildAddress node slot) := by
  intro slot small
  have member:=world.layout.branchLive registered
  have capacity:=world.layout.branchSize node registered
  have before:=world.allocated node member
  have address : branchChildAddress node slot=node+BitVec.ofNat 64 (32+slot*8) := by
   simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
  apply fullDomain
  rw [address,world.layout.field_nat node member (32+slot*8) (by omega)]
  have:=world.capped;omega
 obtain ⟨post,child,slot,run,result,nextNode,valid,nextSlot,typed,nextLevel,advanced,bounded,go,memory,globals,clock,backlink⟩:=
  evaluate_mptInsert_branch_descent_backlink s live extensions branches world.registry node key level keyLength registered
   atNode atKey atLevel fits nibbles keyDomain childDomains oldResult atResult oldNode atNextNode oldSlot atNextSlot
   oldLevel atNextLevel oldGo atGo
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertBranchDescent
 rw [run] at metadata
 exact ⟨post,child,slot,run,world.after_memory_globals memory globals,
  nibbles.after_frame memory metadata.2.1 metadata.2.2.1,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals,clock⟩

#print axioms mpt_insert_branch_descent_slot_world
end InitECandidate.Runtime
