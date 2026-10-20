import InitECandidate.Runtime.AllocatedTriePathsConstructorReach
import InitECandidate.Runtime.TrieNodePathsContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual returned original extension constructor body preserves the whole
allocated trie, exact kind tags and stored paths. Real allocation guards earn
its new record; no successful-callee, heap-room or frame premise is supplied. -/
theorem node_new_ext_body_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer nib length child : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (nonzero : length≠0) (childValid : child=0∨child∈live)
 (atNib : s.locals.lookup (ofString "nib")=some (.val (.word nib)))
 (atLength : s.locals.lookup (ofString "nlen")=some (.val (.word length)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_ext)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧
 AllocatedTrieWorld post (insert pointer live) (insert pointer extensions) branches
  (Function.update size pointer 56) (allocationEnd pointer 56) ∧
 TrieNodeKinds post (insert pointer live) (insert pointer extensions) branches ∧
 TrieNodePaths post (insert pointer live) (insert pointer extensions) branches
  (Function.update size pointer 56) (allocationEnd pointer 56) ∧
 (∀key len,TriePathBuffer s live size key len pointer→
  TriePathBuffer post (insert pointer live) (Function.update size pointer 56) key len (allocationEnd pointer 56)) := by
 obtain ⟨returned,kind,nibAt,lengthAt,childAt,globals,extent,capped,aligned,memory,domain,endian,installed⟩:=
  node_new_ext_returned_context s post pointer nib length child value atNib atLength atChild
   world.heap world.capped fullDomain code run
 have older:=world.registry.after_word_frame (fun address owned=>memory address (world.owned_below address owned))
 have ordered : ExtensionRecordOrder post pointer := by
  intro next zero loaded
  have empty : length=0:=HolWordLab.word.inj (lengthAt.symm.trans zero)
  exact False.elim (nonzero empty)
 have registered:=TrieWalkRegistry.insert_extension post live extensions branches pointer child older kind ordered childAt childValid
 let ready:=setVarHOLFinite (ofString "new_ext") (.val (.word pointer)) {post with locals:=s.locals}
 have fresh : NodeNewExtDeclarationReady s ready (ofString "new_ext") pointer nib length child live extensions branches := by
  refine ⟨?_,?_,kind,nibAt,lengthAt,childAt,globals,extent,capped,aligned,memory,domain,endian,installed,registered.after_memory rfl⟩
  · simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key separate
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm separate]
 have worldOut:=fresh.allocated_world world nonzero
 have kindsOut:=fresh.node_kinds world kinds
 have pathsOut:=fresh.node_paths world paths keyPath short
 refine ⟨returned,worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rfl)
 · intro key len path
   exact (fresh.path_buffer world path).after_context rfl rfl rfl

#print axioms node_new_ext_body_returned_world
end InitECandidate.Runtime
