import InitECandidate.Runtime.MptInsertExtensionSplitTailWorld
import InitECandidate.Runtime.NodeNewExtAssignmentAllocationFloor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real extension-split continuation preserves both the allocated path world and its lower allocation boundary, including the optional fresh extension. -/
theorem mpt_insert_extension_split_tail_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length matched branch oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (matchedBound : matched.toNat≤length.toNat)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (branchLive : branch∈live)
 (atKey : s.locals.lookup (ofString "seg")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertExtensionSplitTail=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions branches newSize finish ∧
 TrieNodeKinds post larger newExtensions branches ∧TrieNodePaths post larger newExtensions branches newSize finish ∧
 TrieAllocationFloor post larger branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→post.locals.lookup other=s.locals.lookup other) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .lower (.const 0) (.var .local (ofString "pl")))=
   some (.val (.word (if 0<matched.toNat then 1#64 else 0#64))) := by
  simp [evalHOLExact,atMatched,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
 rw [source_mptInsert_extension_split_tail,evaluateHOLFiniteState_ite,cmp] at run
 by_cases positive : 0<matched.toNat
 · simp only [if_pos positive,show (1#64)≠0 from by decide,if_false] at run
   have prefixPath : TriePathBuffer s live size key matched frontier := by
    have sliced:=keyPath.slice (start:=0#64) (count:=matched) (by change 0+matched.toNat≤length.toNat;omega)
    simpa using sliced
   have nonzero : matched≠0:=by intro zero;rw [zero] at positive;contradiction
   obtain ⟨assigned,worldOut,kindsOut,pathsOut,transport,locals⟩:=node_new_ext_assignment_world s post
    live extensions branches size frontier key matched branch world kinds paths prefixPath
    (by omega) nonzero (Or.inr branchLive) (ofString "r") _
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atMatched,atBranch]) fullDomain code run
   have lowerOut:=node_new_ext_assignment_allocation_floor s post live extensions branches size frontier key matched branch
    world kinds paths prefixPath (by omega) floor lower heapAbove keyAbove nonzero (Or.inr branchLive) (ofString "r") _
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atMatched,atBranch]) fullDomain code run
   exact ⟨frontier,insert frontier live,insert frontier extensions,Function.update size frontier 56,allocationEnd frontier 56,
    assigned,Or.inl rfl,(fun _ h=>Or.inr h),(fun _ h=>Or.inr h),worldOut,kindsOut,pathsOut,lowerOut,transport,locals⟩
 · simp only [if_neg positive,ite_true] at run
   have actual:=evaluate_local_word_assignment s (ofString "r") (.var .local (ofString "br")) oldResult branch
    atResult (by simpa only [evalHOLExact] using atBranch)
   have same : post=setVarHOLFinite (ofString "r") (.val (.word branch)) s:=(Prod.mk.inj (run.symm.trans actual)).2
   subst post
   refine ⟨branch,live,extensions,size,frontier,?_,branchLive,(fun _ h=>h),(fun _ h=>h),
    world.after_memory_globals rfl rfl,?_,paths.after_context rfl rfl rfl,lower.after_memory rfl,?_,?_⟩
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · exact kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
   · intro nib len path;exact path.after_context rfl rfl rfl
   · intro other different
     simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

#print axioms mpt_insert_extension_split_tail_floor_world
end InitECandidate.Runtime
