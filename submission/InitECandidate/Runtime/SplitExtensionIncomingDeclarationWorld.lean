import InitECandidate.Runtime.SplitExtensionIncomingTailWorld
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual kal declaration derives the remaining key length from source
locals and propagates the complete returned trie world through its scope. -/
theorem split_extension_incoming_declaration_returned_world {F : Type}
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
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 4≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 7)=(some (.returned returned),post)) :
 returned=.val (.word branch) ∧
 ∃larger : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧AllocatedTrieWorld post larger extensions branches newSize finish ∧
 TrieNodeKinds post larger extensions branches ∧TrieNodePaths post larger extensions branches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 rw [source_split_extension_7] at run
 obtain ⟨found,output,initialized,bodyRun,postEq⟩:=evaluate_dec_returned_scope s post (ofString "kal") .one
  (.op .sub [.var .local (ofString "rl"),.var .local (ofString "pl")]) (splitExtensionAt 8) returned run
 have initializer : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .sub [.var .local (ofString "rl"),.var .local (ofString "pl")])=some (.val (.word suffix)) := by
  simp [evalHOLExact,evalListHOLExact,atLength,atMatched,suffixEq,wordOpHOL,wordOp,valueIsWord,valueWord]
 have foundEq : found=.val (.word suffix):=Option.some.inj (initialized.symm.trans initializer)
 subst found
 let ready:=setVarHOLFinite (ofString "kal") (.val (.word suffix)) s
 change evaluateHOLFiniteState ready (splitExtensionAt 8)=(some (.returned returned),output) at bodyRun
 have readyLocal (name : MlS) (separate : name≠ofString "kal") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,separate,Ne.symm separate]
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
 obtain ⟨returnedEq,larger,newSize,finish,sub,worldOut,kindsOut,pathsOut,transport⟩:=
  split_extension_incoming_tail_returned_world ready output live extensions branches size
   frontier branch key length matched suffix value valueLength readyWorld readyKinds
   (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl) short matchedBound suffixEq member
   ((readyLocal _ (by decide)).trans atBranch) ((readyLocal _ (by decide)).trans atKey)
   ((readyLocal _ (by decide)).trans atMatched)
   (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide)).trans atValue) ((readyLocal _ (by decide)).trans atValueLength)
   fullDomain code budget returned bodyRun
 have memory : post.memory=output.memory:=by rw [postEq]
 have globals : post.globals=output.globals:=by rw [postEq]
 have domain : post.memaddrs=output.memaddrs:=by rw [postEq]
 have endian : post.be=output.be:=by rw [postEq]
 refine ⟨returnedEq,larger,newSize,finish,sub,worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [memory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domain endian

#print axioms split_extension_incoming_declaration_returned_world
end InitECandidate.Runtime
