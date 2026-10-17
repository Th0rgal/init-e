import InitECandidate.Runtime.StateFreshTxConstructorStoreHeap
import InitECandidate.Runtime.StateFreshTxPlan
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateFreshTxRegistryAfter (pointer : BitVec 64) : List (Nat × Nat × Nat) → Set (BitVec 64) → Set (BitVec 64)
  | [], tables => tables
  | (width,capacity,_) :: rest, tables =>
    stateFreshTxRegistryAfter (stateFreshTxNextTable pointer width capacity) rest (insert pointer tables)

def stateFreshTxFrontierAfter (pointer : BitVec 64) : List (Nat × Nat × Nat) → BitVec 64
  | [] => pointer
  | (width,capacity,_) :: rest => stateFreshTxFrontierAfter (stateFreshTxNextTable pointer width capacity) rest

/-- Fixed widths follow the deterministic constructor addresses. Capacities
and offsets retain their literal source bounds rather than wrapping in words. -/
def StateFreshTxPlan (widths : BitVec 64 → BitVec 64) (pointer : BitVec 64) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (width,capacity,offset) :: rest =>
    widths pointer = BitVec.ofNat 64 width ∧ width ≤ 52 ∧ capacity < 2 ^ 64 ∧ 1 < capacity ∧ offset < 72 ∧
      (∃ bits, capacity = 2 ^ bits) ∧ StateFreshTxPlan widths (stateFreshTxNextTable pointer width capacity) rest

/-- Execute the actual ordered assignment/store sequence and expose its exact
continuation state, preserving the enlarged registry and all metadata. -/
theorem evaluate_stateFreshTx_constructor_sequence {F : Type} (widths : BitVec 64 → BitVec 64)
    (specs : List (Nat × Nat × Nat)) :
    ∀ (state : PanSemStateFiniteExact 64 F) (pointer ts oldValue : BitVec 64) (tables : Set (BitVec 64)),
    StateFreshTxPlan widths pointer specs →
    (∀ table ∈ tables, RollbackTableReady widths table state) → RollbackPhysicalSeparated widths tables state →
    state.code = originalRuntimeCode → state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) →
    state.globals.lookup (ofString "ts") = some (.val (.word ts)) → state.locals.lookup (ofString "t") = some (.val (.word oldValue)) →
    pointer.toNat % 8 = 0 → ts.toNat + 72 ≤ pointer.toNat →
    (∀ table ∈ tables, ts.toNat + 72 ≤ table.toNat) →
    (∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) →
    pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 → stateFreshTxClockBudget specs ≤ state.clock →
    ∃ post, (∀ tail, evaluateHOLFiniteState state (stateFreshTxConstructorSequence specs tail) = evaluateHOLFiniteState post tail) ∧
      (∀ table ∈ stateFreshTxRegistryAfter pointer specs tables, RollbackTableReady widths table post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter pointer specs tables) post ∧
      (∀ table ∈ stateFreshTxRegistryAfter pointer specs tables, ts.toNat + 72 ≤ table.toNat) ∧
      (∃ value, post.locals.lookup (ofString "t") = some (.val (.word value))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (stateFreshTxFrontierAfter pointer specs))) ∧
      state.clock ≤ post.clock + stateFreshTxClockBudget specs ∧ post.clock ≤ state.clock := by
  induction specs with
  | nil =>
    intro state pointer ts oldValue tables plan family apart code heap tsGlobal tLocal aligned header headers domain space ticks
    exact ⟨state,(fun _ => rfl),family,apart,headers,⟨oldValue,tLocal⟩,rfl,rfl,rfl,HeapGlobalsFrame.refl state,heap,by omega,by omega⟩
  | cons spec rest ih =>
    obtain ⟨width,capacity,offset⟩ := spec
    intro state pointer ts oldValue tables plan family apart code heap tsGlobal tLocal aligned header headers domain space ticks
    obtain ⟨widthEq,widthBound,capacityBound,large,offsetBound,⟨bits,power⟩,restPlan⟩ := plan
    have capacityNat : (BitVec.ofNat 64 capacity).toNat = capacity := Nat.mod_eq_of_lt capacityBound
    have widthNat : (BitVec.ofNat 64 width).toNat = width := Nat.mod_eq_of_lt (by omega)
    have stepSpace : pointer.toNat + 81 * capacity + 114 ≤ 33806089496 := by
      change pointer.toNat + (81 * capacity + 114 + stateFreshTxAllocationBudget rest) ≤ _ at space
      omega
    have bounds := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound stepSpace
    obtain ⟨middle,step,midFamily,midApart,midHeaders,midLocal,_,midCode,midDomain,midEndian,midGlobals,midHeap,cost,remaining⟩ :=
      evaluate_stateFreshTx_constructor_store_heap state widths tables (.const (BitVec.ofNat 64 width)) (.const (BitVec.ofNat 64 capacity))
        pointer (BitVec.ofNat 64 capacity) bits
        (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,widthEq])
        (by rw [capacityNat]; exact power) code (by change capacity + 8 + stateFreshTxClockBudget rest ≤ state.clock at ticks; omega)
        heap (by rw [widthEq,widthNat]; exact widthBound) aligned (by rw [capacityNat]; exact stepSpace)
        (by rw [capacityNat]; exact large) family apart oldValue tLocal ts offset tsGlobal offsetBound domain header headers
    have nextHeap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (stateFreshTxNextTable pointer width capacity))) := by
      simpa only [stateFreshTxNextTable,widthEq] using midHeap
    have nextDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → middle.memaddrs address := by rw [midDomain]; exact domain
    have nextSpace : (stateFreshTxNextTable pointer width capacity).toNat + stateFreshTxAllocationBudget rest ≤ 33806089496 := by
      change pointer.toNat + (81 * capacity + 114 + stateFreshTxAllocationBudget rest) ≤ _ at space
      omega
    have nextTicks : stateFreshTxClockBudget rest ≤ middle.clock := by
      change capacity + 8 + stateFreshTxClockBudget rest ≤ state.clock at ticks
      rw [capacityNat] at cost
      omega
    obtain ⟨post,tailRun,postFamily,postApart,postHeaders,postLocal,postCode,postDomain,postEndian,postGlobals,postHeap,tailCost,tailRemaining⟩ :=
      ih middle (stateFreshTxNextTable pointer width capacity) ts pointer (insert pointer tables) restPlan midFamily midApart
        (midCode.trans code) nextHeap ((midGlobals (ofString "ts") (by decide)).trans tsGlobal) midLocal bounds.2.2 (by omega)
        midHeaders nextDomain nextSpace nextTicks
    refine ⟨post,?_,postFamily,postApart,postHeaders,postLocal,postCode.trans midCode,postDomain.trans midDomain,
      postEndian.trans midEndian,midGlobals.trans postGlobals,postHeap,?_,by omega⟩
    · intro tail
      change evaluateHOLFiniteState state (.seq _ (.seq _ (stateFreshTxConstructorSequence rest tail))) = _
      rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780]
      unfold stateFreshTxPointerStore
      rw [step]
      exact tailRun tail
    · change state.clock ≤ post.clock + (capacity + 8 + stateFreshTxClockBudget rest)
      rw [capacityNat] at cost
      omega

#print axioms evaluate_stateFreshTx_constructor_sequence
end InitECandidate.Runtime
