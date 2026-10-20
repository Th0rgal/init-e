import InitECandidate.Runtime.FreshBranchPayloadWords
import InitECandidate.Runtime.NodeNewBranchReturnedPayload
import InitECandidate.Runtime.AllocatedTriePathsConstructorReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original branch declaration earns allocated world, kinds,
stored paths and word-valued payloads jointly. Both new payload cells are
proved from the actual returned constructor, not an assumed postcondition. -/
theorem allocated_branch_payload_paths_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (pointer : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (payload : TriePayloadWords s live extensions branches)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 41≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_branch") [] tail)
  (fun next=>NodeNewBranchDeclarationReady s next name pointer live extensions branches ∧
   AllocatedTrieWorld next (insert pointer live) extensions (insert pointer branches)
    (Function.update size pointer 176) (allocationEnd pointer 176) ∧
   TrieNodeKinds next (insert pointer live) extensions (insert pointer branches) ∧
   TrieNodePaths next (insert pointer live) extensions (insert pointer branches)
    (Function.update size pointer 176) (allocationEnd pointer 176) ∧
   TriePayloadWords next (insert pointer live) extensions (insert pointer branches)) 41 tail := by
 have installed : s.code.lookup (ofString "node_new_branch")=some
  ([],sourceFunctionBody Guest.guestFn_node_new_branch,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewBranch_lookup
 have lookup:=pan_no_args_lookup s.code.lookup (ofString "node_new_branch")
  (sourceFunctionBody Guest.guestFn_node_new_branch) installed
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some []:=rfl
 have bounded : RunBounded (callEntryStateHOLFinite s HolFiniteMapExact.empty)
  (sourceFunctionBody Guest.guestFn_node_new_branch) 40:=
   runBounded_node_new_branch_body _ code (by change 40≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "node_new_branch") .one .one [] [] _ _ HolFiniteMapExact.empty 40 _
  args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,kind,children,globals,extent,finish,postAligned,memory,domain,endian,keptCode⟩:=
  node_new_branch_returned_context (callEntryStateHOLFinite s HolFiniteMapExact.empty) post pointer value
   world.heap world.capped world.aligned fullDomain code run
 obtain ⟨valueAt,lengthAt⟩:=node_new_branch_returned_payload (callEntryStateHOLFinite s HolFiniteMapExact.empty)
  post pointer value world.heap world.capped world.aligned fullDomain code run
 have older:=world.registry.after_word_frame (fun address owned=>memory address (world.owned_below address owned))
 have registered:=TrieWalkRegistry.insert_branch post live extensions branches pointer older kind children
 subst value
 let next:=setVarHOLFinite name (.val (.word pointer)) {post with locals:=s.locals}
 have fresh : NodeNewBranchDeclarationReady s next name pointer live extensions branches := by
  refine ⟨?_,?_,kind,children,globals,extent,finish,postAligned,memory,domain,endian,keptCode,registered.after_memory rfl⟩
  · simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key separate
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm separate]
 exact ⟨fresh,fresh.allocated_world world,fresh.node_kinds world kinds,fresh.node_paths world paths,
  fresh.payload_words world paths payload valueAt lengthAt⟩

#print axioms allocated_branch_payload_paths_reaches
end InitECandidate.Runtime
