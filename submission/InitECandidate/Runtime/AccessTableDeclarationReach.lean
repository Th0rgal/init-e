import InitECandidate.Runtime.NodedbConstructorReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Real accessed-set constructor endpoint, including all earlier memory,
the actual empty table and its arrays, and a nondecreasing in-arena heap. -/
def AccessTableReady {F : Type} (before : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer keyLength : BitVec 64) (next : PanSemStateFiniteExact 64 F) : Prop :=
 next.locals.lookup name=some (.val (.word pointer)) ∧
 (∀key,key≠name→next.locals.lookup key=before.locals.lookup key) ∧
 next.code=before.code ∧next.memaddrs=before.memaddrs ∧next.be=before.be ∧
 (∀watched : BitVec 64,watched.toNat<pointer.toNat→next.memory watched=before.memory watched) ∧
 HeapRel before.globals next.globals ∧
 ∃keys stride used values order orderPos : BitVec 64,
  HtabAligned keyLength pointer keys stride 8 used values order orderPos 0 3 next ∧
  keys.toNat+8*stride.toNat≤values.toNat ∧OrderInv next 8 0 used order orderPos ∧
  ∃heap : BitVec 64,next.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
   orderPos.toNat+8*8≤heap.toNat ∧heap.toNat%8=0 ∧heap.toNat≤33806089496

/-- The actual `aa = htab_new(20,8)` and `ak = htab_new(52,8)` declaration
forms used by system transactions. Allocation failures are included, with no
reserve, successful-callee or runtime callback premise. -/
theorem access_table_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (keyLength pointer : BitVec 64) (continuation : ProgHOL 64)
 (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (arena : ∀a : BitVec 64,a.toNat%8=0→pointer.toNat≤a.toNat→a.toNat<33806089496→s.memaddrs a)
 (small : keyLength.toNat<2^28) (budget : 49≤s.clock) :
 Reaches s (.decCall name .one (ofString "htab_new") [.const keyLength,.const 8] continuation)
  (AccessTableReady s name pointer keyLength) 49 continuation := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word (8#64)))
 let entry:=callEntryStateHOLFinite s callee
 have keyLocal : entry.locals.lookup (ofString "key_len")=some (.val (.word keyLength)) := by
  simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have capLocal : entry.locals.lookup (ofString "cap")=some (.val (.word (8#64))) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have bound : RunBounded entry (sourceFunctionBody Guest.guestFn_htab_new) 48 := by
  have original:=evaluate_htabNew_body_bounded entry keyLength 8 pointer code keyLocal capLocal atHeap aligned capped
   (by have le:=htabNewCost_le_capacity (8#64);change htabNewCost (8#64)≤s.clock-1;change htabNewCost (8#64)≤48 at le;omega)
  exact original.weaken (htabNewCost_le_capacity (8#64))
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const keyLength,.const 8]=
  some [.val (.word keyLength),.val (.word (8#64))] := by rw [evalListHOLFinite_eq_toExact];rfl
 apply bounded_decCall_reaches s name (ofString "htab_new") .one .one [.const keyLength,.const 8]
  [.val (.word keyLength),.val (.word (8#64))] (sourceFunctionBody Guest.guestFn_htab_new) continuation callee 48
  (AccessTableReady s name pointer keyLength) args (htabNew_installed s keyLength 8 code) budget bound
 intro value output run checked
 obtain ⟨keys,stride,used,values,order,orderPos,valueEq,inv,keysBefore,ordered,domain,endian,frame,
  finalHeap,finalBinding,extent,finalAligned,finalCapped⟩:=htabNew_returned_topV entry output value keyLength 8 pointer 3
   code keyLocal capLocal atHeap aligned capped arena (by decide) small (by change 21≤s.clock-1;omega) run
 have rel:=normalRel_apply htabNew_normalRel (X:=entry)
  (by rw [run];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) code
 rw [run] at rel
 let next:=setVarHOLFinite name value {output with locals:=s.locals}
 have ready : AccessTableReady s name pointer keyLength next := by
  refine ⟨?_,?_,?_,domain,endian,frame,rel,keys,stride,used,values,order,orderPos,?_,keysBefore,?_,
   finalHeap,finalBinding,extent,finalAligned,finalCapped⟩
  · simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,valueEq]
  · intro key different
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · exact inv.code.trans code.symm
  · exact inv.transfer rfl rfl rfl rfl
  · exact ordered.transfer rfl rfl rfl
 exact ready
#print axioms access_table_declaration_reaches
end InitECandidate.Runtime
