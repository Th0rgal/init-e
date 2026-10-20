import InitECandidate.Runtime.MptNewReturnedContext
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.TrieWalkRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
structure MptNewEmptyReady {F : Type} (base next : PanSemStateFiniteExact 64 F) (name : MlS) (pointer : BitVec 64) : Prop where
 atPointer : next.locals.lookup name=some (.val (.word pointer))
 locals : ∀key,key≠name→next.locals.lookup key=base.locals.lookup key
 root : next.memory pointer=.word 0
 secured : next.memory (pointer+8)=.word 0
 globals : next.globals=base.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 16)))
 extent : pointer.toNat+16≤(allocationEnd pointer 16).toNat
 aligned : (allocationEnd pointer 16).toNat%8=0
 capped : (allocationEnd pointer 16).toNat≤33806089496
 memory : ∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=base.memory watched
 domain : next.memaddrs=base.memaddrs
 code : next.code=base.code
 registry : TrieWalkRegistry ∅ ∅ ∅ next

/-- Actual mpt_new(0,0), as used by build_mpt_indexed, reaches a concrete
empty trie with the empty live-node registry or terminates in three clocks.
The header and frontier facts come from the actual returned constructor. -/
theorem mpt_new_empty_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer : BitVec 64) (tail : ProgHOL 64) (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "mpt_new") [.const 0,.const 0] tail)
  (fun next=>MptNewEmptyReady s next name pointer) 3 tail := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (HolFiniteMapExact.empty.update (ofString "root_node",.val (.word (0#64)))).update (ofString "secured",.val (.word (0#64)))
 let entry:=callEntryStateHOLFinite s callee
 have rootLocal : entry.locals.lookup (ofString "root_node")=some (.val (.word (0#64))) := by
  simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have securedLocal : entry.locals.lookup (ofString "secured")=some (.val (.word (0#64))) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const 0,.const 0]=
  some [.val (.word (0#64)),.val (.word (0#64))] := by rw [evalListHOLFinite_eq_toExact];rfl
 have installed : s.code.lookup (ofString "mpt_new")=some ([(ofString "root_node",.one),(ofString "secured",.one)],sourceFunctionBody Guest.guestFn_mpt_new,.one) := by
  rw [code];exact originalRuntimeCode_mptNew_lookup
 have lookup:=pan_two_word_lookup s.code.lookup (ofString "mpt_new") (ofString "root_node") (ofString "secured")
  (sourceFunctionBody Guest.guestFn_mpt_new) 0 0 (by decide) installed
 have bound : RunBounded entry (sourceFunctionBody Guest.guestFn_mpt_new) 2:=mpt_new_body_bounded entry code (by change 2≤s.clock-1;omega)
 apply bounded_decCall_reaches s name (ofString "mpt_new") .one .one [.const 0,.const 0] _ _ tail callee 2
  (fun next=>MptNewEmptyReady s next name pointer) args lookup budget bound
 intro value output run checked
 obtain ⟨returned,root,secured,globals,extent,aligned,newCapped,memory,domain,endian,installedKept⟩:=
  mpt_new_returned_context entry output pointer 0 0 value rootLocal securedLocal atHeap capped code run
 let next:=setVarHOLFinite name value {output with locals:=s.locals}
 have registry : TrieWalkRegistry ∅ ∅ ∅ next := by
  constructor <;>intro node member <;>simp at member
 refine ⟨?_,?_,root,secured,globals,extent,aligned,newCapped,memory,domain,installedKept,registry⟩
 · simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,returned]
 · intro key different
   simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
#print axioms mpt_new_empty_declaration_reaches
end InitECandidate.Runtime
