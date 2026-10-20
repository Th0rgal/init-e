import InitECandidate.Runtime.SplitExtensionNewSideWorld
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.HtabDelFrame
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final incoming arm and return preserve the complete trie and
return the live branch pointer, including real lexical restoration. -/
theorem split_extension_incoming_tail_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch key length matched suffix value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (short : length.toNat≤18) (matchedBound : matched.toNat≤length.toNat)
 (suffixEq : suffix=length-matched)
 (member : branch∈branches)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "kal")=some (.val (.word suffix)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 4≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 8)=(some (.returned returned),post)) :
 returned=.val (.word branch) ∧
 ∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧AllocatedTrieWorld post larger extensions branches newSize finish ∧
 TrieNodeKinds post larger extensions branches ∧TrieNodePaths post larger extensions branches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have nonreturn : ∀state : PanSemStateFiniteExact 64 F,∀value,
  (evaluateHOLFiniteState state splitExtensionNewSide).1≠some (.returned value) := by
  intro state value
  apply evaluate_noTopReturn
  rfl
 rw [source_split_extension_8] at run
 obtain ⟨middle,sideRun,returnRun⟩:=seq_returned_of_nonreturning_first (nonreturn s) run
 obtain ⟨larger,newSize,finish,sub,worldOut,kindsOut,pathsOut,transport⟩:=split_extension_new_side_normal_world
  s middle live extensions branches size frontier branch key length matched suffix value valueLength
  world kinds paths keyPath short matchedBound suffixEq member atBranch atKey atMatched atSuffix atValue atValueLength
  fullDomain code budget sideRun
 have locals : middle.locals=s.locals := by
  apply HolFiniteMapExact.ext
  funext name
  have supported : avoidsLocal name splitExtensionNewSide=true := by
   simp [splitExtensionNewSide,branchPayloadStores,avoidsLocal]
  have kept:=evaluate_avoidsLocal_flowing name _ supported s
  rw [sideRun] at kept
  exact kept (Or.inl rfl)
 have branchAt : middle.locals.lookup (ofString "br")=some (.val (.word branch)):=by rw [locals];exact atBranch
 have returnExact : evaluateHOLFiniteState middle (.return (.var .local (ofString "br")))=
  (some (.returned (.val (.word branch))),emptyLocalsHOLFinite middle) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,branchAt,shapeOfHOLExact]
 have same:=Prod.mk.inj (returnRun.symm.trans returnExact)
 have returnedEq : returned=.val (.word branch):=PanSemResultExact.returned.inj (Option.some.inj same.1)
 have postEq : post=emptyLocalsHOLFinite middle:=same.2
 subst post
 refine ⟨returnedEq,larger,newSize,finish,sub,worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rfl)
 · intro nib len path
   exact (transport nib len path).after_context rfl rfl rfl

#print axioms split_extension_incoming_tail_returned_world
end InitECandidate.Runtime
