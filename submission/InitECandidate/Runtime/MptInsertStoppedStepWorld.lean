import InitECandidate.Runtime.MptInsertSelectedFinishStoppedWorld
import InitECandidate.Runtime.PanZeroDecNormalScope
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every stopped complete original iteration preserves the enlarged trie
world and all paths. This includes all four declarations, the go reset,
real node selection, constructors, commit and lexical restoration. -/
theorem mpt_insert_step_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength slot oldRoot : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeValid : node=0 ∨node∈live) (capacity : node∈live→32≤size node)
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
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 rw [source_mptInsert_step] at run
 obtain ⟨outR,runR,scopeR⟩:=evaluate_zero_dec_normal_scope s post (ofString "r") _ run
 let first:=setVarHOLFinite (ofString "r") (.val (.word (0#64))) s
 change evaluateHOLFiniteState first _=(none,outR) at runR
 obtain ⟨outN,runN,scopeN⟩:=evaluate_zero_dec_normal_scope first outR (ofString "next_node") _ runR
 let second:=setVarHOLFinite (ofString "next_node") (.val (.word (0#64))) first
 change evaluateHOLFiniteState second _=(none,outN) at runN
 obtain ⟨outS,runS,scopeS⟩:=evaluate_zero_dec_normal_scope second outN (ofString "next_slot") _ runN
 let third:=setVarHOLFinite (ofString "next_slot") (.val (.word (0#64))) second
 change evaluateHOLFiniteState third _=(none,outS) at runS
 obtain ⟨output,runL,scopeL⟩:=evaluate_zero_dec_normal_scope third outS (ofString "next_level") _ runS
 let fourth:=setVarHOLFinite (ofString "next_level") (.val (.word (0#64))) third
 change evaluateHOLFiniteState fourth (.seq (.assign .local (ofString "go") (.const (0#64))) mptInsertSelectedFinish)=(none,output) at runL
 obtain ⟨reset,resetRun,coreRun⟩:=seq_normal_parts runL
 obtain ⟨resetValue,resetEval,resetEq⟩:=evaluate_local_assign_normal_value fourth reset (ofString "go") (.const (0#64)) resetRun
 have resetZero : resetValue=.val (.word (0#64)):=Option.some.inj resetEval.symm
 subst resetValue
 subst reset
 let entered:=setVarHOLFinite (ofString "go") (.val (.word (0#64))) fourth
 change evaluateHOLFiniteState entered mptInsertSelectedFinish=(none,output) at coreRun
 have kept (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") (e : name≠ofString "go") :
  entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,fourth,third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,d,e,
   Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e]
 have restored (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") :
  post.locals.lookup name=output.locals.lookup name := by
  rw [scopeR,saved_local_lookup_other outR.locals (ofString "r") name _ a]
  rw [scopeN,saved_local_lookup_other outN.locals (ofString "next_node") name _ b]
  rw [scopeS,saved_local_lookup_other outS.locals (ofString "next_slot") name _ c]
  rw [scopeL,saved_local_lookup_other output.locals (ofString "next_level") name _ d]
 have outputStopped : output.locals.lookup (ofString "go")=some (.val (.word (0#64))) :=
  (restored _ (by decide) (by decide) (by decide) (by decide)).symm.trans stopped
 have atZero : entered.locals.lookup (ofString "r")=some (.val (.word (0#64))) := by
  simp (config:={decide:=true}) [entered,fourth,third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,assigned,valid,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,transport⟩:=
  mpt_insert_selected_finish_stopped_paths_world entered output live extensions branches size frontier node key length level
   value valueLength 0 slot oldRoot (world.after_memory_globals rfl rfl)
   (kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl))
   (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short nodeValid capacity atZero inside
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atNode)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atKey)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atLength)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atLevel)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atValue)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atValueLength)
   fullDomain code budget
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atSlot)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atRoot)
   rootValid (by intro nonzero;exact (typedSlot nonzero).after_length_frame (by intro current member;rfl))
   outputStopped coreRun
 have memory : post.memory=output.memory:=by rw [scopeR,scopeN,scopeS,scopeL]
 have globals : post.globals=output.globals:=by rw [scopeR,scopeN,scopeS,scopeL]
 have domains : post.memaddrs=output.memaddrs:=by rw [scopeR,scopeN,scopeS,scopeL]
 have endian : post.be=output.be:=by rw [scopeR,scopeN,scopeS,scopeL]
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans assigned,valid,sub,extSub,branchSub,
  worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domains endian,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;exact congrFun memory current)
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domains endian

#print axioms mpt_insert_step_stopped_paths_world
end InitECandidate.Runtime
