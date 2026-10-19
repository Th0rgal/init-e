import InitECandidate.Runtime.NodedbCapacityPrefixReach
import InitECandidate.Runtime.HtabBlockInit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_nodedb_constructor : nodedbAt 2 =
    .decCall (ofString "t") .one (ofString "htab_new") [.const 32,.var .local (ofString "cap")] (nodedbAt 3) := rfl

/-- The actual database constructor's normal continuation has an empty aligned
table, ordered arrays below the final heap, and the earlier input memory intact. -/
def NodedbTableReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (bits : Nat) (next : PanSemStateFiniteExact 64 F) : Prop :=
  next.locals.lookup (ofString "t") = some (.val (.word pointer)) ∧
  (∀ key : MlS, key ≠ ofString "t" → next.locals.lookup key = state.locals.lookup key) ∧
  next.code = state.code ∧ next.memaddrs = state.memaddrs ∧ next.be = state.be ∧
  (∀ watched : BitVec 64, watched.toNat < pointer.toNat → next.memory watched = state.memory watched) ∧
  HeapRel state.globals next.globals ∧
  ∃ keys stride used values order orderPos : BitVec 64,
    HtabAligned 32 pointer keys stride capacity used values order orderPos 0 bits next ∧
    keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat ∧
    OrderInv next capacity 0 used order orderPos ∧
    ∃ heap : BitVec 64, next.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      orderPos.toNat + capacity.toNat * 8 ≤ heap.toNat ∧ heap.toNat % 8 = 0 ∧ heap.toNat ≤ 33806089496

theorem htabNewCost_le_capacity (capacity : BitVec 64) : htabNewCost capacity ≤ capacity.toNat + 40 := by
  unfold htabNewCost
  omega

/-- All outcomes of the original database constructor are bounded; allocation
failure needs no reserve assumption. A normal return exposes the real table
invariant to the remaining insertion loop. -/
theorem runBounded_nodedb_constructor {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity : BitVec 64) (bits tailCost : Nat)
    (code : state.code = originalRuntimeCode)
    (atCap : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits)
    (budget : capacity.toNat + 40 + 1 + tailCost ≤ state.clock)
    (tail : ∀ next, NodedbTableReady state pointer capacity bits next → tailCost ≤ next.clock →
      RunBounded next (nodedbAt 3) tailCost) :
    RunBounded state (nodedbAt 2) (capacity.toNat + 40 + 1 + tailCost) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const 32,.var .local (ofString "cap")] = some [.val (.word (32#64)),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atCap]
  rw [source_nodedb_constructor]
  refine RunBounded.decCall (bodyCost := capacity.toNat + 40) args budget ?_
  intro body callee returnShape lookup
  rw [htabNew_installed state (32#64) capacity code] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32#64)))).update (ofString "cap",.val (.word capacity)))
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (32#64))) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : capacity.toNat + 40 ≤ entry.clock := by change _ ≤ state.clock - 1; omega
  have bounded := (evaluate_htabNew_body_bounded entry (32#64) capacity pointer code keyLocal capLocal atHeap aligned capped
    ((htabNewCost_le_capacity capacity).trans entryBudget)).weaken (htabNewCost_le_capacity capacity)
  refine ⟨bounded,?_⟩
  intro value output run remaining
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
  exact tail next ready remaining

#print axioms source_nodedb_constructor
#print axioms htabNewCost_le_capacity
#print axioms runBounded_nodedb_constructor
end InitECandidate.Runtime
