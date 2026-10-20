import InitECandidate.Runtime.MptInsertExtensionDispatchWorld
import InitECandidate.Runtime.MptInsertBranchDispatchWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Every continuing actual kind choice follows a registered extension or
branch and prepares a strictly higher key level with a live child backlink. -/
theorem mpt_insert_kind_choice_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length kind oldResult oldNode oldSlot oldLevel : BitVec 64)
 (member : node∈live)
 (atKind : s.locals.lookup (ofString "k")=some (.val (.word kind)))
 (kindField : s.memory node=.word kind) (nonzero : kind≠0#64)
 (nibbles : TrieNibbleRange s key length)
 (keyExtent : key.toNat+length.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 20≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertKindChoice=(none,post)) :
 ∃child slot nextLevel : BitVec 64, AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNibbleRange post key length ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word slot)) ∧
 post.memory slot=.word child ∧TrieChildSlot post extensions branches slot ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)) ∧
 level.toNat<nextLevel.toNat ∧nextLevel.toNat≤length.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals := by
 rcases mpt_insert_kind_choice_running s post kind atKind zero running run with ⟨extension,actual⟩|⟨nonleaf,nonextension,actual⟩
 · have registered : node∈extensions:=world.registry.extensionKind node member (by simpa [extension] using kindField)
   obtain ⟨segment,child,worldOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals⟩:=
    mpt_insert_extension_dispatch_world s post live extensions branches size frontier world node key level length oldResult oldNode oldSlot oldLevel
     registered atNode atKey atLevel atLength atResult atNextNode atNextSlot atNextLevel zero inside short code budget running actual
   have metadata:=evaluateHOLFiniteState_metadata s mptInsertExtensionDispatch
   rw [actual] at metadata
   exact ⟨child,node+BitVec.ofNat 64 48,level+segment,worldOut,
    nibbles.after_frame memory metadata.2.1 metadata.2.2.1,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals⟩
 · have registered : node∈branches:=world.registry.branchKind node member kind kindField nonzero nonleaf nonextension
   obtain ⟨child,slot,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals,_⟩:=
    mpt_insert_branch_dispatch_world s post live extensions branches size frontier world node key level length oldResult oldNode oldSlot oldLevel
     registered atNode atKey atLevel atLength inside nibbles keyExtent fullDomain atResult atNextNode atNextSlot atNextLevel zero running actual
   exact ⟨child,slot,level+1,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevel,advanced,bounded,go,memory,globals⟩

#print axioms mpt_insert_kind_choice_world
end InitECandidate.Runtime
