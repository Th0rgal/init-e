import InitECandidate.Runtime.AllocatedTrieWorld
import InitECandidate.Runtime.TrieBranchValueStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem AllocatedTrieWorld.write_branch_slot {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent child : BitVec 64) (registered : parent∈branches) (slot : Nat) (small : slot<16)
 (childValid : child=0 ∨child∈live) :
 AllocatedTrieWorld (sourceWriteWord s (branchChildAddress parent slot) child)
  live extensions branches size frontier := by
 obtain ⟨kinds,lengths,_⟩:=world.layout.branch_slot_separate parent registered slot small
 exact world.write_child _ _ childValid kinds lengths

theorem AllocatedTrieWorld.write_branch_value {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent value : BitVec 64) (registered : parent∈branches) (offset : Nat)
 (large : 160≤offset) (small : offset<176) :
 AllocatedTrieWorld (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value)
  live extensions branches size frontier := by
 have registry:=world.registry.write_branch_value s live extensions branches size world.layout parent value registered offset large small
 have positive : TriePositiveExtensions extensions (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) := by
  apply world.positive.after_length_frame
  intro node member
  have separate:=world.layout.fields_ne node parent (world.layout.extensionLive member) (world.layout.branchLive registered)
   40 offset (by have:=world.layout.extensionSize node member;omega)
   (by have:=world.layout.branchSize parent registered;omega) (Or.inr (by omega))
  change (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value).memory (node+40#64)=s.memory (node+40#64)
  simp [sourceWriteWord,separate]
 exact ⟨registry,positive,world.layout,world.allocated,world.heap,world.capped,world.aligned⟩

/-- The real byte-indexed branch-child store used after a fresh leaf call in
_create_branch_from_two_leaves. Its actual loaded byte selects a valid slot;
record separation protects every other node's kind and extension length. -/
theorem allocated_trie_branch_byte_store {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (branchName keyName childName : MlS) (parent key child : BitVec 64) (byte : UInt8)
 (branchLocal : s.locals.lookup branchName=some (.val (.word parent)))
 (keyLocal : s.locals.lookup keyName=some (.val (.word key)))
 (childLocal : s.locals.lookup childName=some (.val (.word child)))
 (registered : parent∈branches) (childValid : child=0 ∨child∈live)
 (loaded : @panMemLoadByteHOL 64 _ s.memory s.memaddrs
  (fun a=>Classical.propDecidable (s.memaddrs a)) s.be key=some byte)
 (small : byte.toNat<16)
 (domain : s.memaddrs (branchChildAddress parent byte.toNat)) :
 let statement : ProgHOL 64 := .store (.op .add [.var .local branchName,.const 32,
  .panop .mul [.loadByte (.var .local keyName),.const 8]]) (.var .local childName)
 let post:=sourceWriteWord s (branchChildAddress parent byte.toNat) child
 evaluateHOLFiniteState s statement=(none,post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧
 post.memory (branchChildAddress parent byte.toNat)=.word child ∧post.clock=s.clock ∧post.locals=s.locals := by
 have address : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.var .local branchName,.const 32,.panop .mul [.loadByte (.var .local keyName),.const 8]])=
  some (.val (.word (branchChildAddress parent byte.toNat))) := by
  simp [evalHOLExact,evalListHOLExact,branchLocal,keyLocal,loaded,wordOpHOL,wordOp,panOpHOL,
   valueIsWord,valueWord,branchChildAddress,BitVec.add_assoc]
 refine ⟨evaluate_store_word s _ child _ (.var .local childName) address childLocal domain,
  world.write_branch_slot parent child registered byte.toNat small childValid,?_,rfl,rfl⟩
 simp [sourceWriteWord]

#print axioms AllocatedTrieWorld.write_branch_slot
#print axioms AllocatedTrieWorld.write_branch_value
#print axioms allocated_trie_branch_byte_store
end InitECandidate.Runtime
