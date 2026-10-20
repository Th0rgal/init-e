import InitECandidate.Runtime.MptInsertLeafReturnedWorld
import InitECandidate.Runtime.MptInsertLeafComparisonFloorWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original leaf insertion returned-world proof. The actual allocated
leaf earns both initial field-load domains, and its stored path supplies the
old key and length. Both comparison outcomes and every original constructor
are included, with no future callee/frame/heap-room assumption. -/
theorem mpt_insert_leaf_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (keyAbove : floor≤key.toNat)
 (nodeLive : node∈live) (nonExt : node∉extensions) (nonBranch : node∉branches)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 144≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__insert_into_leaf)=(some (.returned returned),post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 returned=.val (.word root) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 TrieAllocationFloor post larger newBranches floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 obtain ⟨oldKey,oldLength,memoryKey,memoryLength,oldShort,oldPath⟩:=paths.paths node nodeLive nonBranch
 have capacity:=paths.leafCapacity node nodeLive nonExt nonBranch
 have domain (offset : Nat) (small : offset<64) : s.memaddrs (node+BitVec.ofNat 64 offset) := by
  apply fullDomain
  rw [world.layout.field_nat node nodeLive offset (by omega)]
  have allocated:=world.allocated node nodeLive
  have capped:=world.capped
  omega
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (mptInsertLeafAt 0)=(some (.returned returned),post) at run
 obtain ⟨output,tailRun,memory,globals,domains,endian⟩:=mpt_insert_leaf_loads_returned_scope s post node oldKey oldLength
  atNode (domain 32 (by decide)) (domain 40 (by decide)) memoryKey memoryLength returned run
 let ready:=mptInsertLeafLoadedState s oldKey oldLength
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 have readyLocal (name : MlS) (ek : name≠ofString "ek") (el : name≠ofString "el") :
  ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,mptInsertLeafLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
   ek,Ne.symm ek,el,Ne.symm el]
 obtain ⟨root,larger,newExtensions,newBranches,newSize,finish,valueEq,rootLive,sub,extSub,branchSub,
  worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=
  mpt_insert_leaf_comparison_returned_floor_world ready output live extensions branches size frontier node oldKey oldLength key length
   value valueLength readyWorld readyKinds (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
   short floor (lower.after_memory rfl) heapAbove keyAbove nodeLive nonExt nonBranch memoryKey memoryLength
   ((readyLocal _ (by decide) (by decide)).trans atNode)
   (by simp (config:={decide:=true}) [ready,mptInsertLeafLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [ready,mptInsertLeafLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide) (by decide)).trans atKey)
   ((readyLocal _ (by decide) (by decide)).trans atLength)
   ((readyLocal _ (by decide) (by decide)).trans atValue)
   ((readyLocal _ (by decide) (by decide)).trans atValueLength)
   fullDomain code budget returned tailRun
 refine ⟨root,larger,newExtensions,newBranches,newSize,finish,valueEq,rootLive,sub,extSub,branchSub,
  worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domains endian,lowerOut.after_memory memory,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro current member;rw [memory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domains endian

#print axioms mpt_insert_leaf_returned_floor_world
end InitECandidate.Runtime
