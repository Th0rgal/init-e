import InitECandidate.Runtime.MptInsertLeafSource
import InitECandidate.Runtime.NodeNewExtTailReturnedFloorWorld
import InitECandidate.Runtime.PanTailCallTerminal
import InitECandidate.Runtime.TriePathBufferSlice
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual divergent-leaf final arm returns a fresh extension for a nonempty
common prefix, otherwise the existing branch. The original tail call cannot
fall through; both outcomes retain the complete allocated trie. -/
theorem mpt_insert_leaf_tail_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier key length matched branch : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (matchedBound : matched.toNat≤length.toNat)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (branchLive : branch∈live)
 (atKey : s.locals.lookup (ofString "ek")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (mptInsertLeafAt 5)=(some (.returned value),post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 value=.val (.word root) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions branches newSize finish ∧
 TrieNodeKinds post larger newExtensions branches ∧TrieNodePaths post larger newExtensions branches newSize finish ∧
 TrieAllocationFloor post larger branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .lower (.const 0) (.var .local (ofString "pl")))=
   some (.val (.word (if 0<matched.toNat then 1#64 else 0#64))) := by
  simp [evalHOLExact,atMatched,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
 rw [source_mpt_insert_leaf_5,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cmp] at run
 by_cases positive : 0<matched.toNat
 · simp only [if_pos positive,show (1#64)≠0 from by decide,if_false] at run
   let arguments : List (ExpHOL 64):=[.var .local (ofString "ek"),.var .local (ofString "pl"),.var .local (ofString "br")]
   have callRun : evaluateHOLFiniteState s (.call none (ofString "node_new_ext") arguments)=(some (.returned value),post) := by
    cases evaluated : evaluateHOLFiniteState s (.call none (ofString "node_new_ext") arguments) with
    | mk result output=>
     dsimp only [arguments] at evaluated
     rw [evaluated] at run
     cases result with
     | none=>
      have terminal:=evaluate_tail_call_terminal s (ofString "node_new_ext") arguments
      rw [evaluated] at terminal
      exact False.elim (terminal rfl)
     | some result=>exact run
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
    some [.val (.word key),.val (.word matched),.val (.word branch)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atMatched,atBranch]
   have prefixPath : TriePathBuffer s live size key matched frontier := by
    have sliced:=keyPath.slice (start:=0#64) (count:=matched) (by change 0+matched.toNat≤length.toNat;omega)
    simpa using sliced
   have nonzero : matched≠0:=by intro zero;rw [zero] at positive;contradiction
   obtain ⟨returned,worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=node_new_ext_tail_returned_floor_world
    s post live extensions branches size frontier key matched branch world kinds paths prefixPath
    (by omega) floor lower heapAbove keyAbove nonzero (Or.inr branchLive) arguments args fullDomain code value callRun
   exact ⟨frontier,insert frontier live,insert frontier extensions,Function.update size frontier 56,allocationEnd frontier 56,
    returned,Or.inl rfl,fun _ h=>Or.inr h,fun _ h=>Or.inr h,worldOut,kindsOut,pathsOut,lowerOut,transport⟩
 · simp only [if_neg positive,ite_true,evaluateHOLFiniteState_skip] at run
   have returnExact : evaluateHOLFiniteState s (.return (.var .local (ofString "br")))=
    (some (.returned (.val (.word branch))),emptyLocalsHOLFinite s) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,atBranch,shapeOfHOLExact]
   change evaluateHOLFiniteState s (.return (.var .local (ofString "br")))=(some (.returned value),post) at run
   have same:=Prod.mk.inj (run.symm.trans returnExact)
   have returned : value=.val (.word branch):=PanSemResultExact.returned.inj (Option.some.inj same.1)
   have postEq : post=emptyLocalsHOLFinite s:=same.2
   subst post
   refine ⟨branch,live,extensions,size,frontier,returned,branchLive,fun _ h=>h,fun _ h=>h,
    world.after_memory_globals rfl rfl,?_,paths.after_context rfl rfl rfl,lower.after_memory rfl,?_⟩
   · exact kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
   · intro nib len path
     exact path.after_context rfl rfl rfl

#print axioms mpt_insert_leaf_tail_returned_floor_world
end InitECandidate.Runtime
