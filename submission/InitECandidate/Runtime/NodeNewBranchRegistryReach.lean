import InitECandidate.Runtime.NodeNewBranchReturnedContext
import InitECandidate.Runtime.NodeNewBranchUniformBound
import InitECandidate.Runtime.OriginalNodeNewBranchCode
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.TrieWalkRegistryWordFrame
import InitECandidate.Runtime.TrieWalkRegistryInsertBranch
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure NodeNewBranchDeclarationReady {F : Type} (base next : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer : BitVec 64) (live extensions branches : Set (BitVec 64)) : Prop where
 atPointer : next.locals.lookup name=some (.val (.word pointer))
 locals : ∀key,key≠name→next.locals.lookup key=base.locals.lookup key
 kind : next.memory pointer=.word 3
 children : ∀slot : Nat,slot<16→next.memory (branchChildAddress pointer slot)=.word 0
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 176)))
 extent : pointer.toNat+176≤(allocationEnd pointer 176).toNat
 capped : (allocationEnd pointer 176).toNat≤33806089496
 aligned : (allocationEnd pointer 176).toNat%8=0
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched
 domain : next.memaddrs=base.memaddrs
 endian : next.be=base.be
 code : next.code=base.code
 registry : TrieWalkRegistry (insert pointer live) extensions (insert pointer branches) next

/-- The installed original constructor either establishes a fresh null-child
branch and preserves every old registry word, or aborts within41 source clocks.
The allocation extent is derived from the actual allocator return. -/
theorem node_new_branch_registry_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (pointer : BitVec 64) (live extensions branches : Set (BitVec 64))
 (heap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 41≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_branch") [] tail)
  (fun next=>NodeNewBranchDeclarationReady s next name pointer live extensions branches) 41 tail := by
 have installed : s.code.lookup (ofString "node_new_branch")=some
  ([],sourceFunctionBody Guest.guestFn_node_new_branch,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewBranch_lookup
 have lookup:=pan_no_args_lookup s.code.lookup (ofString "node_new_branch")
  (sourceFunctionBody Guest.guestFn_node_new_branch) installed
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some [] := rfl
 have bounded : RunBounded (callEntryStateHOLFinite s HolFiniteMapExact.empty)
  (sourceFunctionBody Guest.guestFn_node_new_branch) 40 :=
  runBounded_node_new_branch_body _ code (by change 40≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "node_new_branch") .one .one [] [] _ _ HolFiniteMapExact.empty 40 _
  args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,kind,children,globals,extent,finish,postAligned,memory,domain,endian,keptCode⟩:=
  node_new_branch_returned_context (callEntryStateHOLFinite s HolFiniteMapExact.empty) post pointer value
   heap capped aligned fullDomain code run
 have older:=registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))
 have registered:=TrieWalkRegistry.insert_branch post live extensions branches pointer older kind children
 refine ⟨?_,?_,kind,children,globals,extent,finish,postAligned,memory,domain,endian,keptCode,registered.after_memory rfl⟩
 · simp [returned,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms node_new_branch_registry_declaration_reaches
end InitECandidate.Runtime
