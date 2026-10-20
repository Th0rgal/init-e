import InitECandidate.Runtime.MptInsertKindDispatchStoppedWorld
import InitECandidate.Runtime.MptInsertNodeLoad
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The entire stopped non-null source arm includes its actual kind load and
scope restoration before producing the terminal root and preserved paths. -/
theorem mpt_insert_nonnull_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength oldResult : BitVec 64)
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
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertNonNullStep=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have sourceForm : mptInsertNonNullStep=
  .dec (ofString "k") .one (.load .one (mptInsertNodeAddress 0)) mptInsertKindDispatch := by
  simp only [mptInsertNonNullStep,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
   Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
 rw [sourceForm] at run
 obtain ⟨kindValue,output,evaluated,dispatchRun,scope⟩:=evaluate_dec_normal_scope s post (ofString "k") .one _ _ run
 obtain ⟨kind,kindEq,kindField,_⟩:=mpt_insert_node_load_word s node 0 kindValue atNode evaluated
 subst kindValue
 have realKind : s.memory node=.word kind:=by simpa using kindField
 let entered:=setVarHOLFinite (ofString "k") (.val (.word kind)) s
 have kept (name : MlS) (different : name≠ofString "k") : entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 have restored (name : MlS) (different : name≠ofString "k") : post.locals.lookup name=output.locals.lookup name := by
  rw [scope]
  exact saved_local_lookup_other output.locals (ofString "k") name _ different
 have outputStopped : output.locals.lookup (ofString "go")=some (.val (.word (0#64))) :=
  (restored _ (by decide)).symm.trans stopped
 have atKind : entered.locals.lookup (ofString "k")=some (.val (.word kind)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,result,liveRoot,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,transport⟩:=
  mpt_insert_kind_dispatch_stopped_paths_world entered output live extensions branches size frontier
   node key length level value valueLength kind oldResult (world.after_memory_globals rfl rfl)
   (kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl))
   (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short nodeLive capacity realKind atKind
   ((kept _ (by decide)).trans atResult) inside ((kept _ (by decide)).trans atNode)
   ((kept _ (by decide)).trans atKey) ((kept _ (by decide)).trans atLength)
   ((kept _ (by decide)).trans atLevel) ((kept _ (by decide)).trans atValue)
   ((kept _ (by decide)).trans atValueLength) fullDomain code budget outputStopped dispatchRun
 have memory : post.memory=output.memory:=by rw [scope]
 have globals : post.globals=output.globals:=by rw [scope]
 have domains : post.memaddrs=output.memaddrs:=by rw [scope]
 have endian : post.be=output.be:=by rw [scope]
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,(restored _ (by decide)).trans result,
  liveRoot,sub,extSub,branchSub,worldOut.after_memory_globals memory globals,?_,
  pathsOut.after_context memory domains endian,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [memory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domains endian

#print axioms mpt_insert_nonnull_stopped_paths_world
end InitECandidate.Runtime
