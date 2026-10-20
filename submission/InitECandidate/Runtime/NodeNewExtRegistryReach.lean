import InitECandidate.Runtime.NodeNewExtReturnedContext
import InitECandidate.Runtime.NodeNewExtUniformBound
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.TrieWalkRegistryWordFrame
import InitECandidate.Runtime.TrieWalkRegistryInsertExtension
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure NodeNewExtDeclarationReady {F : Type} (base next : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer nib length child : BitVec 64) (live extensions branches : Set (BitVec 64)) : Prop where
 atPointer : next.locals.lookup name=some (.val (.word pointer))
 locals : ∀key,key≠name→next.locals.lookup key=base.locals.lookup key
 kind : next.memory pointer=.word 2
 nibAt : next.memory (pointer+32)=.word nib
 lengthAt : next.memory (pointer+40)=.word length
 childAt : next.memory (pointer+48)=.word child
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 56)))
 extent : pointer.toNat+56≤(allocationEnd pointer 56).toNat
 capped : (allocationEnd pointer 56).toNat≤33806089496
 aligned : (allocationEnd pointer 56).toNat%8=0
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched
 domain : next.memaddrs=base.memaddrs
 endian : next.be=base.be
 code : next.code=base.code
 registry : TrieWalkRegistry (insert pointer live) (insert pointer extensions) branches next

/-- An actual extension declaration registers its real child and protects all
older traversal words. Positive length or an older child gives zero-length
progress; fresh allocation room is derived from the original guard. -/
theorem node_new_ext_registry_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length child : BitVec 64) (live extensions branches : Set (BitVec 64))
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word child)])
 (heap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (registry : TrieWalkRegistry live extensions branches s)
 (ownedBelow : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat)
 (childValid : child=0 ∨ child∈live) (progress : length≠0 ∨ child.toNat<pointer.toNat)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_ext") arguments tail)
  (fun next=>NodeNewExtDeclarationReady s next name pointer nib length child live extensions branches) 3 tail := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update (ofString "nlen",.val (.word length))).update
   (ofString "child",.val (.word child))
 have installed : s.code.lookup (ofString "node_new_ext")=some
  ([(ofString "nib",.one),(ofString "nlen",.one),(ofString "child",.one)],sourceFunctionBody Guest.guestFn_node_new_ext,.one) := by
  rw [code];exact originalRuntimeCode_nodeNewExt_lookup
 have lookup:=pan_three_word_lookup s.code.lookup (ofString "node_new_ext")
  (ofString "nib") (ofString "nlen") (ofString "child") (sourceFunctionBody Guest.guestFn_node_new_ext)
  nib length child (by decide) (by decide) (by decide) installed
 have bounded : RunBounded (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_node_new_ext) 2 :=
  node_new_ext_uniform_bounded _ code (by change 2≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "node_new_ext") .one .one arguments _ _ tail callee 2 _ args lookup budget bounded
 intro value post run checked
 obtain ⟨returned,kind,nibAt,lengthAt,childAt,globals,extent,finish,postAligned,memory,domain,endian,keptCode⟩:=
  node_new_ext_returned_context (callEntryStateHOLFinite s callee) post pointer nib length child value
   (by simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   heap capped fullDomain code run
 have older:=registry.after_word_frame (fun address owned=>memory address (ownedBelow address owned))
 have ordered : ExtensionRecordOrder post pointer := by
  intro next zero loaded
  have sameChild : child=next:=HolWordLab.word.inj (childAt.symm.trans loaded)
  have sameLength : length=0:=HolWordLab.word.inj (lengthAt.symm.trans zero)
  rcases progress with positive|before
  · exact False.elim (positive sameLength)
  · simpa [←sameChild] using before
 have registered:=TrieWalkRegistry.insert_extension post live extensions branches pointer child older kind ordered childAt childValid
 refine ⟨?_,?_,kind,nibAt,lengthAt,childAt,globals,extent,finish,postAligned,memory,domain,endian,keptCode,registered.after_memory rfl⟩
 · simp [returned,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro key different
   simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms node_new_ext_registry_declaration_reaches
end InitECandidate.Runtime
