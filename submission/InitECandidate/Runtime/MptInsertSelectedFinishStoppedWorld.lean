import InitECandidate.Runtime.MptInsertNewLeafFinishWorld
import InitECandidate.Runtime.MptInsertNonNullFinishStoppedWorld
import InitECandidate.Runtime.MptInsertSelectedFinishWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All stopped original node selections and the complete finish preserve
paths and commit a valid root, including fresh null-node allocation. -/
theorem mpt_insert_selected_finish_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength oldResult slot oldRoot : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeValid : node=0 ∨node∈live) (capacity : node∈live→32≤size node)
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
 (run : evaluateHOLFiniteState s mptInsertSelectedFinish=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 unfold mptInsertSelectedFinish at run
 obtain ⟨selected,selection,finishRun⟩:=seq_normal_parts run
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "node")) (.const (0#64)))=
  some (.val (.word (if node=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atNode,Compiler.Encoders.Asm.wordCmpHOL]
 rw [evaluateHOLFiniteState_ite,cmp] at selection
 by_cases zero : node=0#64
 · have actual : evaluateHOLFiniteState s mptInsertNewLeafCall=(none,selected) := by
    simpa only [if_pos zero,show (1#64)≠0 from by decide,if_false] using selection
   have joined:=evaluate_seq_none actual finishRun
   obtain ⟨root,assigned,valid,finalWorld,finalKinds,finalPaths,transport⟩:=
    mpt_insert_new_leaf_finish_paths_world s post live extensions branches size frontier key length level
     value valueLength slot oldRoot world kinds paths keyPath short inside atKey atLength atLevel atValue atValueLength
     fullDomain code atSlot atRoot rootValid typedSlot joined
   exact ⟨root,insert frontier live,extensions,branches,Function.update size frontier 64,allocationEnd frontier 64,
    assigned,valid,(fun _ h=>Or.inr h),(fun _ h=>h),(fun _ h=>h),finalWorld,finalKinds,finalPaths,transport⟩
 · have zeroRaw : node≠0:=zero
   have actual : evaluateHOLFiniteState s mptInsertNonNullStep=(none,selected) := by
    simpa only [if_neg zeroRaw,show (0#64)=0 from rfl,if_true] using selection
   have member : node∈live:=nodeValid.resolve_left zero
   exact mpt_insert_nonnull_finish_stopped_paths_world s post live extensions branches size frontier node key length level
    value valueLength oldResult slot oldRoot world kinds paths keyPath short member (capacity member) atResult inside
    atNode atKey atLength atLevel atValue atValueLength fullDomain code budget atSlot atRoot rootValid typedSlot
    stopped (evaluate_seq_none actual finishRun)

#print axioms mpt_insert_selected_finish_stopped_paths_world
end InitECandidate.Runtime
