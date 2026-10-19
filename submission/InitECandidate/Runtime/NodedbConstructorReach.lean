import InitECandidate.Runtime.NodedbConstructorBound
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The real constructor reaches its suffix with its execution-derived table,
heap, workspace and old-memory frame, or terminates within its proved budget. -/
theorem nodedb_constructor_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode)
    (atCap : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits)
    (budget : capacity.toNat + 40 + 1 ≤ state.clock) :
    Reaches state (nodedbAt 2) (NodedbTableReady state pointer capacity bits)
      (capacity.toNat + 40 + 1) (nodedbAt 3) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const 32,.var .local (ofString "cap")] = some [.val (.word (32#64)),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atCap]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32#64)))).update (ofString "cap",.val (.word capacity)))
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (32#64))) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : capacity.toNat + 40 ≤ entry.clock := by change _ ≤ state.clock - 1; omega
  have bounded := (evaluate_htabNew_body_bounded entry (32#64) capacity pointer code keyLocal capLocal atHeap aligned capped
    ((htabNewCost_le_capacity capacity).trans entryBudget)).weaken (htabNewCost_le_capacity capacity)
  rw [source_nodedb_constructor]
  apply bounded_decCall_reaches state (ofString "t") (ofString "htab_new") .one .one
    [.const 32,.var .local (ofString "cap")] [.val (.word (32#64)),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) (nodedbAt 3)
    ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32#64)))).update (ofString "cap",.val (.word capacity)))
    (capacity.toNat + 40) _ args (htabNew_installed state (32#64) capacity code) budget bounded
  intro value output run checked
  obtain ⟨keys,stride,used,values,order,orderPos,valueEq,inv,keysBefore,ordered,domain,endian,frame,
    finalHeap,finalBinding,extent,finalAligned,finalCapped⟩ :=
    htabNew_returned_topV entry output value (32#64) capacity pointer bits code keyLocal capLocal atHeap aligned capped
      arena power (by decide) (by omega) run
  have rel := normalRel_apply htabNew_normalRel (X := entry)
    (by rw [run]; exact Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))) code
  rw [run] at rel
  let next := setVarHOLFinite (ofString "t") value {output with locals := state.locals}
  have ready : NodedbTableReady state pointer capacity bits next := by
    refine ⟨?_,?_,?_,domain,endian,frame,rel,keys,stride,used,values,order,orderPos,?_,keysBefore,?_,
      finalHeap,finalBinding,extent,finalAligned,finalCapped⟩
    · simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,valueEq]
    · intro key different
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    · exact inv.code.trans code.symm
    · exact inv.transfer rfl rfl rfl rfl
    · exact ordered.transfer rfl rfl rfl
  exact ready

#print axioms nodedb_constructor_reaches
end InitECandidate.Runtime
