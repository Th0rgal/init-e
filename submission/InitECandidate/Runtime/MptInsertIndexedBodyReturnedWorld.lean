import InitECandidate.Runtime.MptInsertBodyReturnedScope
import InitECandidate.Runtime.MptInsertLoopNormalPaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original insertion function returns its committed root and
preserves the actual allocated world and paths through all initializers,
iterations, final return and lexical scope restorations. -/
theorem mpt_insert_indexed_body_returned_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier node key length level valuePointer valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (inside : level.toNat≤length.toNat)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__mpt_insert_node)=(some (.returned returned),post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 returned=.val (.word root) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 TriePathBuffer post larger newSize key length finish := by
 let ready:=setVarHOLFinite (ofString "go") (.val (.word (1#64)))
  (setVarHOLFinite (ofString "slot") (.val (.word (0#64)))
   (setVarHOLFinite (ofString "result") (.val (.word (0#64))) s))
 have kept (name : MlS) (a : name≠ofString "go") (b : name≠ofString "slot") (c : name≠ofString "result") :
  ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
 have active : MptInsertActive ready live extensions branches size frontier key length valuePointer valueLength (length.toNat-level.toNat+1) := by
  refine ⟨world.after_memory_globals rfl rfl,keyPath.nibbles.after_frame rfl rfl rfl,fullDomain,
   (kept _ (by decide) (by decide) (by decide)).trans atKey,
   (kept _ (by decide) (by decide) (by decide)).trans atLength,
   (kept _ (by decide) (by decide) (by decide)).trans atValue,
   (kept _ (by decide) (by decide) (by decide)).trans atValueLength,node,0,level,0,
   (kept _ (by decide) (by decide) (by decide)).trans atNode,?_,
   (kept _ (by decide) (by decide) (by decide)).trans atLevel,?_,nodeValid,Or.inl rfl,?_,?_,inside,rfl⟩
  · simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro impossible;exact False.elim (impossible rfl)
  · intro impossible;exact False.elim (impossible rfl)
 have strong : MptInsertPathsActive ready live extensions branches size frontier key length valuePointer valueLength
  (length.toNat-level.toNat+1) :=
  ⟨active,kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl),
   paths.after_context rfl rfl rfl,keyPath.after_context rfl rfl rfl⟩
 obtain ⟨loopPost,output,loopRun,returnRun,memoryScope,globalsScope,domainsScope,endianScope⟩:=
  mpt_insert_body_returned_scope s post returned run
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,rootAt,rootValid,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,keyOut⟩:=
  mpt_insert_indexed_loop_normal_paths ready loopPost live extensions branches size frontier key length valuePointer valueLength
   _ strong capacity recordsBefore aligned keyExtent short code budget loopRun
 have actualReturn : evaluateHOLFiniteState loopPost (.return (.var .local (ofString "result")))=
  (some (.returned (.val (.word root))),emptyLocalsHOLFinite loopPost) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,rootAt,shapeOfHOLExact,sizeOfShapeWithContextHOL]
 have same:=Prod.mk.inj (returnRun.symm.trans actualReturn)
 have returnedEq : returned=.val (.word root):=PanSemResultExact.returned.inj (Option.some.inj same.1)
 have outputEq : output=emptyLocalsHOLFinite loopPost:=same.2
 have memory : post.memory=loopPost.memory:=memoryScope.trans (congrArg (fun state=>state.memory) outputEq)
 have globals : post.globals=loopPost.globals:=globalsScope.trans (congrArg (fun state=>state.globals) outputEq)
 have domains : post.memaddrs=loopPost.memaddrs:=domainsScope.trans (congrArg (fun state=>state.memaddrs) outputEq)
 have endian : post.be=loopPost.be:=endianScope.trans (congrArg (fun state=>state.be) outputEq)
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,returnedEq,rootValid,sub,extSub,branchSub,
  worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domains endian,keyOut.after_context memory domains endian⟩
 exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
  (by intro current member;exact congrFun memory current)

#print axioms mpt_insert_indexed_body_returned_world
end InitECandidate.Runtime
