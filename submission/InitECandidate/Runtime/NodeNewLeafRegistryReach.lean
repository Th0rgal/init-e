import InitECandidate.Runtime.NodeNewLeafReturnedContext
import InitECandidate.Runtime.NodeNewLeafUniformBound
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.TrieWalkRegistryWordFrame
import InitECandidate.Runtime.TrieWalkRegistryInsertTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure NodeNewLeafDeclarationReady {F : Type} (base next : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer nib length valuePointer valueLength : BitVec 64)
 (live extensions branches : Set (BitVec 64)) : Prop where
 atPointer : next.locals.lookup name=some (.val (.word pointer))
 locals : ∀key,key≠name→next.locals.lookup key=base.locals.lookup key
 kind : next.memory pointer=.word 1
 nibAt : next.memory (pointer+32)=.word nib
 lengthAt : next.memory (pointer+40)=.word length
 valueAt : next.memory (pointer+48)=.word valuePointer
 valueLengthAt : next.memory (pointer+56)=.word valueLength
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 64)))
 extent : pointer.toNat+64≤(allocationEnd pointer 64).toNat
 capped : (allocationEnd pointer 64).toNat≤33806089496
 aligned : (allocationEnd pointer 64).toNat%8=0
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched
 domain : next.memaddrs=base.memaddrs
 endian : next.be=base.be
 code : next.code=base.code
 registry : TrieWalkRegistry (insert pointer live) extensions branches next

/-- The real installed constructor adds a terminal node to the traversal
registry, preserving all older trie words, or terminates within three source
clocks. Heap room is earned from the actual allocator guard. -/
theorem node_new_leaf_registry_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length valuePointer valueLength : BitVec 64) (live extensions branches : Set (BitVec 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word valuePointer),.val (.word valueLength)])
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_leaf") arguments tail)
  (fun next=>NodeNewLeafDeclarationReady s next name pointer nib length valuePointer valueLength live extensions branches) 3 tail := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word length))).update
   (ofString "vptr",.val (.word valuePointer))).update (ofString "vlen",.val (.word valueLength))
 let entry:=callEntryStateHOLFinite s callee
 have installed : s.code.lookup (ofString "node_new_leaf")=some
  ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "vptr",.one),(ofString "vlen",.one)],sourceFunctionBody Guest.guestFn_node_new_leaf,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewLeaf_lookup
 have lookup:=pan_four_word_lookup s.code.lookup (ofString "node_new_leaf")
  (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (sourceFunctionBody Guest.guestFn_node_new_leaf)
  nib length valuePointer valueLength (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
 have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_node_new_leaf) 2 :=
  node_new_leaf_uniform_bounded entry code (by change 2≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "node_new_leaf") .one .one arguments _ _ tail callee 2 _ args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,kind,nibAt,lengthAt,valueAt,valueLengthAt,globals,extent,finish,aligned,memory,domain,endian,keptCode⟩:=
  node_new_leaf_returned_context entry post pointer nib length valuePointer valueLength value
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   atHeap capped fullDomain code run
 have older:=registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))
 have registered:=TrieWalkRegistry.insert_terminal post live extensions branches pointer 1 older kind (Or.inr rfl)
 refine ⟨?_,?_,kind,nibAt,lengthAt,valueAt,valueLengthAt,globals,extent,finish,aligned,memory,domain,endian,keptCode,registered.after_memory rfl⟩
 · simp [returned,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms node_new_leaf_registry_declaration_reaches
end InitECandidate.Runtime
