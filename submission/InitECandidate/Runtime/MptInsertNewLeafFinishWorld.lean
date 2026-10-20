import InitECandidate.Runtime.MptInsertNewLeafCallWorld
import InitECandidate.Runtime.MptInsertFinishPathsWorld
import InitECandidate.Runtime.TrieChildSlotPositiveWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual null-node constructor and complete finish compose into a fresh
path-preserving trie world and committed root, with real backlink typing. -/
theorem mpt_insert_new_leaf_finish_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer key length level value valueLength slot oldRoot : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size key length pointer) (short : length.toNat≤18)
 (inside : level.toNat≤length.toNat)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atRoot : s.locals.lookup (ofString "result")=some (.val (.word oldRoot)))
 (rootValid : oldRoot=0 ∨oldRoot∈live)
 (typedSlot : slot≠0→TrieChildSlot s extensions branches slot)
 (run : evaluateHOLFiniteState s (.seq mptInsertNewLeafCall mptInsertFinish)=(none,post)) :
 ∃root : BitVec 64,
 post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈insert pointer live) ∧
 AllocatedTrieWorld post (insert pointer live) extensions branches
  (Function.update size pointer 64) (allocationEnd pointer 64) ∧
 TrieNodeKinds post (insert pointer live) extensions branches ∧
 TrieNodePaths post (insert pointer live) extensions branches
  (Function.update size pointer 64) (allocationEnd pointer 64) ∧
 (∀key len,TriePathBuffer s live size key len pointer→
  TriePathBuffer post (insert pointer live) (Function.update size pointer 64) key len (allocationEnd pointer 64)) := by
 obtain ⟨selected,selection,finishRun⟩:=seq_normal_parts run
 obtain ⟨result,worldOut,kindsOut,pathsOut,transport,locals⟩:=
  mpt_insert_new_leaf_call_world s selected live extensions branches size pointer key length level value valueLength
   world kinds paths keyPath short inside atKey atLength atLevel atValue atValueLength fullDomain code selection
 have slotAt : selected.locals.lookup (ofString "slot")=some (.val (.word slot)):=
  (locals _ (by decide)).trans atSlot
 have rootAt : selected.locals.lookup (ofString "result")=some (.val (.word oldRoot)):=
  (locals _ (by decide)).trans atRoot
 have selectedTyped (nonzero : slot≠0) : TrieChildSlot selected extensions branches slot :=
  (typedSlot nonzero).after_positive_world worldOut (fun _ h=>h) (fun _ h=>h)
 have validRoot : oldRoot=0 ∨oldRoot∈insert pointer live := by
  rcases rootValid with zero|member
  · exact Or.inl zero
  · exact Or.inr (Or.inr member)
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertNewLeafCall
 rw [selection] at metadata
 obtain ⟨root,finalWorld,finalKinds,finalPaths,assigned,valid,finalTransport⟩:=
  mpt_insert_finish_normal_paths_world selected post (insert pointer live) extensions branches
   (Function.update size pointer 64) (allocationEnd pointer 64) worldOut kindsOut pathsOut slot pointer oldRoot
   slotAt result rootAt (Or.inr (Or.inl rfl)) validRoot selectedTyped
   (by intro address bound;rw [metadata.2.1];exact fullDomain address bound) finishRun
 refine ⟨root,assigned,valid,finalWorld,finalKinds,finalPaths,?_⟩
 intro nib len path
 exact finalTransport nib len (transport nib len path)

#print axioms mpt_insert_new_leaf_finish_paths_world
end InitECandidate.Runtime
