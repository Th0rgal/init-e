import InitECandidate.Runtime.MptInsertLeafDispatchWorld
import InitECandidate.Runtime.MptInsertExtensionStoppedWorld
import InitECandidate.Runtime.MptInsertBranchStoppedWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every stopped original node-kind choice produces a registered root and
preserves stored paths and separated input paths, including all constructors. -/
theorem mpt_insert_kind_choice_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength kind oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (nonzero : kind≠0#64)
 (kindField : s.memory node=.word kind)
 (atKind : s.locals.lookup (ofString "k")=some (.val (.word kind)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (inside : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 145≤s.clock)
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertKindChoice=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have cmp (constant : BitVec 64) : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "k")) (.const constant))=
  some (.val (.word (if kind=constant then 1#64 else 0#64))) := by
  simp [evalHOLExact,atKind,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_mptInsert_kind_choice,evaluateHOLFiniteState_ite,cmp] at run
 by_cases leaf : kind=1#64
 · have leafRaw : kind=1:=leaf
   simp only [if_pos leafRaw,show (1#64)≠0 from by decide,if_false] at run
   obtain ⟨nonExt,nonBranch⟩:=kinds.leaf_separate node (by simpa only [leaf] using kindField)
   obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,result,liveRoot,sub,extSub,branchSub,
    worldOut,kindsOut,pathsOut,transport,_⟩:=
    mpt_insert_leaf_dispatch_normal_world s post live extensions branches size frontier node key length level value valueLength
     world kinds paths keyPath short nodeLive nonExt nonBranch inside atNode atKey atLength atLevel
     atValue atValueLength fullDomain code budget run
   exact ⟨root,larger,newExtensions,newBranches,newSize,finish,result,liveRoot,sub,extSub,branchSub,
    worldOut,kindsOut,pathsOut,transport⟩
 · have leafRaw : kind≠1:=leaf
   simp only [if_neg leafRaw,if_pos rfl] at run
   change evaluateHOLFiniteState s (.ite _ mptInsertExtensionDispatch mptInsertBranchDispatch)=(none,post) at run
   rw [evaluateHOLFiniteState_ite,cmp] at run
   by_cases extension : kind=2#64
   · have extensionRaw : kind=2:=extension
     simp only [if_pos extensionRaw,show (1#64)≠0 from by decide,if_false] at run
     have registered : node∈extensions:=world.registry.extensionKind node nodeLive (by simpa [extension] using kindField)
     obtain ⟨root,larger,newExtensions,newSize,finish,result,liveRoot,sub,extSub,
      worldOut,kindsOut,pathsOut,transport,_⟩:=
      mpt_insert_extension_dispatch_stopped_world s post live extensions branches size frontier node key length level
       value valueLength oldResult world kinds paths keyPath short registered inside atNode atKey atLength
       atLevel atValue atValueLength atResult fullDomain code (by omega) stopped run
     exact ⟨root,larger,newExtensions,insert frontier branches,newSize,finish,result,liveRoot,sub,extSub,
      (fun _ h=>Or.inr h),worldOut,kindsOut,pathsOut,transport⟩
   · have extensionRaw : kind≠2:=extension
     simp only [if_neg extensionRaw,if_pos rfl] at run
     have registered : node∈branches:=world.registry.branchKind node nodeLive kind kindField nonzero leaf extension
     obtain ⟨worldOut,kindsOut,pathsOut,result,transport⟩:=
      mpt_insert_branch_dispatch_stopped_paths_world s post live extensions branches size frontier world kinds paths
       node value valueLength oldResult level length registered atNode atValue atValueLength atResult fullDomain
       atLevel atLength stopped run
     exact ⟨node,live,extensions,branches,size,frontier,result,nodeLive,(fun _ h=>h),(fun _ h=>h),
      (fun _ h=>h),worldOut,kindsOut,pathsOut,transport⟩

#print axioms mpt_insert_kind_choice_stopped_paths_world
end InitECandidate.Runtime
