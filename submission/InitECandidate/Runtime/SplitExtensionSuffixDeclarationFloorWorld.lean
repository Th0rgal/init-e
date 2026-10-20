import InitECandidate.Runtime.SplitExtensionChildrenFloorWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual old-suffix declaration computes sl-pl before the checked complete
split tail; the original returned world survives lexical scope restoration. -/
theorem split_extension_suffix_declaration_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch segment segmentLength key length matched child value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (segmentPath : TriePathBuffer s live size segment segmentLength frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (shortSegment : segmentLength.toNat≤18) (shortKey : length.toNat≤18)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (segmentAbove : floor≤segment.toNat) (keyAbove : floor≤key.toNat)
 (member : branch∈branches) (childValid : child=0∨child∈live)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSegmentLength : s.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 7≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 4)=(some (.returned returned),post)) :
 returned=.val (.word branch) ∧
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧extensions⊆newExtensions ∧AllocatedTrieWorld post larger newExtensions branches newSize finish ∧
 TrieNodeKinds post larger newExtensions branches ∧TrieNodePaths post larger newExtensions branches newSize finish ∧
 TrieAllocationFloor post larger branches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 rw [source_split_extension_4] at run
 obtain ⟨found,output,initialized,bodyRun,postEq⟩:=evaluate_dec_returned_scope s post (ofString "sal") .one
  (.op .sub [.var .local (ofString "sl"),.var .local (ofString "pl")]) (splitExtensionAt 5) returned run
 have initializer : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .sub [.var .local (ofString "sl"),.var .local (ofString "pl")])=
   some (.val (.word (segmentLength-matched))) := by
  simp [evalHOLExact,evalListHOLExact,atSegmentLength,atMatched,wordOpHOL,wordOp,valueIsWord,valueWord]
 have foundEq : found=.val (.word (segmentLength-matched)):=Option.some.inj (initialized.symm.trans initializer)
 subst found
 let ready:=setVarHOLFinite (ofString "sal") (.val (.word (segmentLength-matched))) s
 change evaluateHOLFiniteState ready (splitExtensionAt 5)=(some (.returned returned),output) at bodyRun
 have readyLocal (name : MlS) (separate : name≠ofString "sal") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,separate,Ne.symm separate]
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
 obtain ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=
  split_extension_children_returned_floor_world ready output live extensions branches size
   frontier branch segment segmentLength key length matched (segmentLength-matched) child value valueLength
   readyWorld readyKinds (paths.after_context rfl rfl rfl)
   (segmentPath.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
   shortSegment shortKey inside matchedBound rfl floor (lower.after_memory rfl) heapAbove segmentAbove keyAbove member childValid
   ((readyLocal _ (by decide)).trans atBranch) ((readyLocal _ (by decide)).trans atSegment)
   ((readyLocal _ (by decide)).trans atMatched)
   (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide)).trans atChild) ((readyLocal _ (by decide)).trans atKey)
   ((readyLocal _ (by decide)).trans atLength) ((readyLocal _ (by decide)).trans atValue)
   ((readyLocal _ (by decide)).trans atValueLength) fullDomain code budget returned bodyRun
 have memory : post.memory=output.memory:=by rw [postEq]
 have globals : post.globals=output.globals:=by rw [postEq]
 have domain : post.memaddrs=output.memaddrs:=by rw [postEq]
 have endian : post.be=output.be:=by rw [postEq]
 refine ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,lowerOut.after_memory memory,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [memory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domain endian

#print axioms split_extension_suffix_declaration_returned_floor_world
end InitECandidate.Runtime
