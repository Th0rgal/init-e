import InitECandidate.Runtime.MptInsertChoiceStoppedWorld
import InitECandidate.Runtime.MptInsertGuardNormal
import InitECandidate.Runtime.NodeInvalidateKindsWorld
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full stopped source kind dispatch includes its rejection guard and
actual cache invalidation. All path frames and the remaining constructor
budget are earned from those executions. -/
theorem mpt_insert_kind_dispatch_stopped_paths_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength kind oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (capacity : 32≤size node)
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
 (code : s.code=originalRuntimeCode) (budget : 146≤s.clock)
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertKindDispatch=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 rw [source_mptInsert_kind_dispatch] at run
 obtain ⟨guarded,guardRun,tailRun⟩:=seq_normal_parts run
 obtain ⟨nonzero,identity⟩:=mpt_insert_guard_normal_identity s guarded kind atKind code guardRun
 subst guarded
 obtain ⟨ready,invalidateRun,choiceRun⟩:=seq_normal_parts tailRun
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
  [.var .local (ofString "node")]=some [.val (.word node)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNode]
 have actualInvalidate:=invalidateRun
 rw [source_mptInsert_invalidate] at actualInvalidate
 obtain ⟨readyWorld,readyKinds,locals,globals,frame⟩:=
  node_invalidate_discard_normal_kinds_world s ready live extensions branches size frontier node
   world kinds nodeLive capacity _ args fullDomain code actualInvalidate
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertInvalidate
 rw [invalidateRun] at metadata
 have fieldsInside (field : Nat) (included : field∈[8,16,24]) : field<size node := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at included
  rcases included with rfl|rfl|rfl <;>omega
 have fieldsFrame (watched : BitVec 64)
  (separate : ∀field∈[8,16,24],watched≠node+BitVec.ofNat 64 field) :
  ready.memory watched=s.memory watched :=
  frame watched (separate 8 (by simp)) (separate 16 (by simp)) (separate 24 (by simp))
 have readyPaths : TrieNodePaths ready live extensions branches size frontier := by
  apply paths.after_record_fields world node nodeLive [8,16,24] fieldsInside (Or.inr ?_)
   fieldsFrame metadata.2.1 metadata.2.2.1
  intro field included
  simp only [List.mem_cons,List.not_mem_nil,or_false] at included
  rcases included with rfl|rfl|rfl <;>decide
 have transport (nib len : BitVec 64) (path : TriePathBuffer s live size nib len frontier) :
  TriePathBuffer ready live size nib len frontier :=
  path.after_record_fields world node nodeLive [8,16,24] fieldsInside fieldsFrame metadata.2.1 metadata.2.2.1
 have different (offset : Nat) (positive : 0<offset) (small : offset<32) : node≠node+BitVec.ofNat 64 offset := by
  intro equal
  have natural:=congrArg BitVec.toNat equal
  rw [world.layout.field_nat node nodeLive offset (by omega)] at natural
  omega
 have readyKind : ready.memory node=.word kind := by
  rw [frame node (different 8 (by decide) (by decide)) (different 16 (by decide) (by decide)) (different 24 (by decide) (by decide))]
  exact kindField
 have bounded:=mpt_insert_invalidate_bounded s code (by omega)
 unfold RunBounded at bounded
 rw [invalidateRun] at bounded
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,result,liveRoot,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,tailTransport⟩:=
  mpt_insert_kind_choice_stopped_paths_world ready post live extensions branches size frontier node key length level
   value valueLength kind oldResult readyWorld readyKinds readyPaths (transport key length keyPath) short
   nodeLive nonzero readyKind (by rw [locals];exact atKind) (by rw [locals];exact atResult)
   inside (by rw [locals];exact atNode) (by rw [locals];exact atKey) (by rw [locals];exact atLength)
   (by rw [locals];exact atLevel) (by rw [locals];exact atValue) (by rw [locals];exact atValueLength)
   (by intro address bound;rw [metadata.2.1];exact fullDomain address bound)
   (metadata.1.trans code) (by have:=bounded.1;dsimp only at this;omega) stopped choiceRun
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,result,liveRoot,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,?_⟩
 intro nib len path
 exact tailTransport nib len (transport nib len path)

#print axioms mpt_insert_kind_dispatch_stopped_paths_world
end InitECandidate.Runtime
