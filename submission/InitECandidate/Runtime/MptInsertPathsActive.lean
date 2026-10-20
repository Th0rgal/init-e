import InitECandidate.Runtime.TrieNodePathsContext
import InitECandidate.Runtime.MptInsertLoopInvariant
import InitECandidate.Runtime.MptInsertContinuingPathsWorld
import InitECandidate.Runtime.MptInsertLeafMatchedTransport
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Strengthened active invariant for recovering the terminal trie world. -/
structure MptInsertPathsActive {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length value valueLength : BitVec 64) (rank : Nat) : Prop where
 active : MptInsertActive s live extensions branches size frontier key length value valueLength rank
 kinds : TrieNodeKinds s live extensions branches
 paths : TrieNodePaths s live extensions branches size frontier
 keyPath : TriePathBuffer s live size key length frontier

theorem MptInsertPathsActive.decClock {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 {frontier key length value valueLength : BitVec 64} {rank : Nat}
 (current : MptInsertPathsActive s live extensions branches size frontier key length value valueLength rank) :
 MptInsertPathsActive (decClockHOLFinite s) live extensions branches size frontier key length value valueLength rank := by
 exact ⟨current.active.decClock,
  current.kinds.after_kind_frame current.active.world.layout.extensionLive current.active.world.layout.branchLive
   (by intro node member;rfl),current.paths.after_context rfl rfl rfl,current.keyPath.after_context rfl rfl rfl⟩

/-- Every actual continuing non-null iteration keeps the stronger path invariant and
strictly lowers its rank; the three cache writes are the only memory changes. -/
theorem mpt_insert_paths_active_nonnull_step {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length value valueLength : BitVec 64) (rank : Nat)
 (current : MptInsertPathsActive s live extensions branches size frontier key length value valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (nonnull : s.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "node")≠some (.val (.word (0#64))))
 (running : post.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 ∃nextRank,nextRank<rank ∧MptInsertPathsActive post live extensions branches size frontier key length value valueLength nextRank := by
 obtain ⟨nextRank,smaller,nextActive⟩:=mpt_insert_active_step s post live extensions branches size frontier key length value valueLength rank
  current.active capacity recordsBefore aligned keyExtent short code budget running run
 obtain ⟨node,slot,level,root,a,b,c,d,nodeValid,rootValid,typed,backlink,inside,rankEq⟩:=current.active.path
 have nonzero : node≠0 := by
  intro zero
  apply nonnull
  simpa [zero] using a
 have member : node∈live:=nodeValid.resolve_left nonzero
 obtain ⟨kindsOut,pathsOut⟩:=mpt_insert_step_preserves_paths s post live extensions branches size frontier
  current.active.world current.kinds current.paths node key level length slot root member rootValid
  (capacity node) current.keyPath.nibbles aligned (recordsBefore node) keyExtent current.active.domain
  a current.active.atKey c current.active.atLength b d typed backlink inside short code budget running run
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,frame⟩:=
  mpt_insert_step_world s post live extensions branches size frontier current.active.world node key level length slot root
   nodeValid rootValid (capacity node) current.keyPath.nibbles aligned (recordsBefore node) keyExtent current.active.domain
   a current.active.atKey c current.active.atLength b d typed backlink inside short code budget running run
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertLoopStep
 rw [run] at metadata
 refine ⟨nextRank,smaller,nextActive,kindsOut,pathsOut,?_⟩
 apply current.keyPath.after_record_fields current.active.world node member [8,16,24]
 · intro field included
   have cap:=capacity node member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl|rfl <;>omega
 · intro watched separate
   exact frame watched (separate 8 (by simp)) (separate 16 (by simp)) (separate 24 (by simp))
 · exact metadata.2.1
 · exact metadata.2.2.1

#print axioms MptInsertPathsActive.decClock
#print axioms mpt_insert_paths_active_nonnull_step
end InitECandidate.Runtime
