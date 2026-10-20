import InitECandidate.Runtime.MptInsertStepWorld
import InitECandidate.Runtime.TrieNodePathsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The whole actual continuing iteration preserves exact kinds and every
stored key path through node invalidation, idempotent backlink commit, local
updates and all four lexical declaration restorations. -/
theorem mpt_insert_step_preserves_paths {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (node key level length slot root : BitVec 64)
 (member : node∈live) (rootValid : root=0 ∨root∈live)
 (capacity : node∈live →32≤size node)
 (nibbles : TrieNibbleRange s key length)
 (keyAligned : key.toNat%8=0) (recordBefore : node∈live →node.toNat+32≤key.toNat)
 (keyExtent : key.toNat+length.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atRoot : s.locals.lookup (ofString "result")=some (.val (.word root)))
 (typedSlot : slot≠0 →TrieChildSlot s extensions branches slot)
 (oldBacklink : slot≠0 →s.memory slot=.word node)
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier := by
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,frame⟩:=
  mpt_insert_step_world s post live extensions branches size frontier world node key level length slot root
   (Or.inr member) rootValid capacity nibbles keyAligned recordBefore keyExtent fullDomain atNode atKey atLevel
   atLength atSlot atRoot typedSlot oldBacklink inside short code budget running run
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertLoopStep
 rw [run] at metadata
 have recordCapacity:=capacity member
 constructor
 · apply kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
   intro watched registered
   have separate (offset : Nat) (positive : 0<offset) (small : offset<32) : watched≠node+BitVec.ofNat 64 offset := by
    simpa using world.layout.fields_ne watched node registered member 0 offset
     (world.layout.positive watched registered) (by omega) (Or.inr (by omega))
   exact frame watched (separate 8 (by decide) (by decide)) (separate 16 (by decide) (by decide)) (separate 24 (by decide) (by decide))
 · apply paths.after_record_fields world node member [8,16,24]
   · intro field included;simp only [List.mem_cons,List.not_mem_nil,or_false] at included
     rcases included with rfl|rfl|rfl <;>omega
   · right;intro field included;simp only [List.mem_cons,List.not_mem_nil,or_false] at included
     rcases included with rfl|rfl|rfl <;>decide
   · intro watched separate
     exact frame watched (separate 8 (by simp)) (separate 16 (by simp)) (separate 24 (by simp))
   · exact metadata.2.1
   · exact metadata.2.2.1

#print axioms mpt_insert_step_preserves_paths
end InitECandidate.Runtime
