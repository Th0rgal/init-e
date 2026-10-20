import InitECandidate.Runtime.MptInsertFinishIdempotent
import InitECandidate.Runtime.TrieChildSlotMetadataSeparation
import InitECandidate.Runtime.MptInsertBranchDescentWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual finishing suffix installs its prepared traversal state. Its
idempotent backlink commit preserves the entire allocated world and indexed
key, and the real allocated slot extent earns the commit-store domain. -/
theorem evaluate_mptInsert_finish_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node slot level root child nextSlot nextLevel key length : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word node)))
 (atRoot : s.locals.lookup (ofString "result")=some (.val (.word root)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word child)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word nextSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)))
 (atGo : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
 (member : node∈live) (rootValid : root=0 ∨root∈live) (childValid : child=0 ∨child∈live)
 (nextBacklink : s.memory nextSlot=.word child)
 (prepared : TrieChildSlot s extensions branches nextSlot)
 (oldSlot : slot≠0 →TrieChildSlot s extensions branches slot)
 (backlink : slot≠0 →s.memory slot=.word node)
 (nibbles : TrieNibbleRange s key length)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) :
 ∃post nextRoot,evaluateHOLFiniteState s mptInsertFinish=(none,post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNibbleRange post key length ∧
 post.locals.lookup (ofString "result")=some (.val (.word nextRoot)) ∧(nextRoot=0 ∨nextRoot∈live) ∧
 post.locals.lookup (ofString "node")=some (.val (.word child)) ∧
 post.locals.lookup (ofString "slot")=some (.val (.word nextSlot)) ∧TrieChildSlot post extensions branches nextSlot ∧
 post.memory nextSlot=.word child ∧
 post.locals.lookup (ofString "level")=some (.val (.word nextLevel)) ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals ∧post.clock=s.clock ∧
 (∀name,name≠ofString "result" →name≠ofString "node" →name≠ofString "slot" →name≠ofString "level" →
  post.locals.lookup name=s.locals.lookup name) := by
 have domain (nonzero : slot≠0) : s.memaddrs slot := by
  apply fullDomain
  have below:=(oldSlot nonzero).allocated_below s live extensions branches size frontier slot world
  have:=world.capped;omega
 obtain ⟨post,nextRoot,run,registry,clock,rootAt,validRoot,nodeAt,_,slotAt,typedSlot,levelAt,locals⟩:=
  evaluate_mptInsert_finish s live extensions branches size world.layout world.registry node slot level node root child nextSlot nextLevel
   atNode atSlot atLevel atResult atRoot atNextNode atNextSlot atNextLevel (Or.inr member) rootValid childValid prepared oldSlot domain
 obtain ⟨memory,globals⟩:=mpt_insert_finish_idempotent s post slot node atSlot atResult backlink code run
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertFinish
 rw [run] at metadata
 refine ⟨post,nextRoot,run,world.after_memory_globals memory globals,nibbles.after_frame memory metadata.2.1 metadata.2.2.1,rootAt,validRoot,nodeAt,slotAt,typedSlot,?_,levelAt,?_,memory,globals,clock,locals⟩
 · rw [memory];exact nextBacklink
 · exact (locals _ (by decide) (by decide) (by decide) (by decide)).trans atGo

#print axioms evaluate_mptInsert_finish_world
end InitECandidate.Runtime
