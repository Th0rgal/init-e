import InitECandidate.Runtime.MptInsertNonNullStoppedWorld
import InitECandidate.Runtime.MptInsertNonNullLocalFrame
import InitECandidate.Runtime.MptInsertFinishPathsWorld
import InitECandidate.Runtime.TrieChildSlotPositiveWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A complete stopped non-null selection and finish preserves all paths and
commits a live/null root. Backlink typing is derived from the actual enlarged
positive world, even when splitting changes an old extension's length. -/
theorem mpt_insert_nonnull_finish_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength oldResult slot oldRoot : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (capacity : 32≤size node)
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (inside : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 146≤s.clock)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atRoot : s.locals.lookup (ofString "result")=some (.val (.word oldRoot)))
 (rootValid : oldRoot=0 ∨oldRoot∈live)
 (typedSlot : slot≠0→TrieChildSlot s extensions branches slot)
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s (.seq mptInsertNonNullStep mptInsertFinish)=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 obtain ⟨selected,selection,finishRun⟩:=seq_normal_parts run
 have finishGo:=evaluate_avoidsLocal_flowing (ofString "go") mptInsertFinish
  (by rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];decide) selected
 rw [finishRun] at finishGo
 have selectedStopped : selected.locals.lookup (ofString "go")=some (.val (.word (0#64))) :=
  (finishGo (Or.inl rfl)).symm.trans stopped
 obtain ⟨selectedRoot,larger,newExtensions,newBranches,newSize,finish,result,rootLive,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,transport⟩:=
  mpt_insert_nonnull_stopped_paths_world s selected live extensions branches size frontier node key length level
   value valueLength oldResult world kinds paths keyPath short nodeLive capacity atResult inside
   atNode atKey atLength atLevel atValue atValueLength fullDomain code budget selectedStopped selection
 have localFrame:=mpt_insert_nonnull_local_frame s selected selection
 have slotAt : selected.locals.lookup (ofString "slot")=some (.val (.word slot)):=
  (localFrame _ (by simp [mptInsertStableNames])).trans atSlot
 have rootAt : selected.locals.lookup (ofString "result")=some (.val (.word oldRoot)):=
  (localFrame _ (by simp [mptInsertStableNames])).trans atRoot
 have selectedTyped (nonzero : slot≠0) : TrieChildSlot selected newExtensions newBranches slot :=
  (typedSlot nonzero).after_positive_world worldOut extSub branchSub
 have selectedRootValid : oldRoot=0 ∨oldRoot∈larger := by
  rcases rootValid with zero|member
  · exact Or.inl zero
  · exact Or.inr (sub member)
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertNonNullStep
 rw [selection] at metadata
 obtain ⟨root,finalWorld,finalKinds,finalPaths,assigned,valid,finalTransport⟩:=
  mpt_insert_finish_normal_paths_world selected post larger newExtensions newBranches newSize finish
   worldOut kindsOut pathsOut slot selectedRoot oldRoot slotAt result rootAt (Or.inr rootLive) selectedRootValid
   selectedTyped (by intro address bound;rw [metadata.2.1];exact fullDomain address bound) finishRun
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,assigned,valid,sub,extSub,branchSub,
  finalWorld,finalKinds,finalPaths,?_⟩
 intro nib len path
 exact finalTransport nib len (transport nib len path)

#print axioms mpt_insert_nonnull_finish_stopped_paths_world
end InitECandidate.Runtime
