import InitECandidate.Runtime.StateFreshTxSequenceMemoryFrame
import InitECandidate.Runtime.StateFreshTxFieldLoads
import InitECandidate.Runtime.StateFreshTxConstructorStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem StateFreshTxPlan.offset_bound (widths : BitVec 64 → BitVec 64)
    (specs : List (Nat × Nat × Nat)) :
    ∀ pointer, StateFreshTxPlan widths pointer specs → ∀ spec ∈ specs, spec.2.2 < 72 := by
  induction specs with
  | nil => simp
  | cons head rest ih =>
    rcases head with ⟨width,capacity,offset⟩
    intro pointer plan spec member
    rcases List.mem_cons.mp member with same | later
    · subst spec; exact plan.2.2.2.2.1
    · exact ih _ plan.2.2.2.2.2.2 spec later

/-- Execute the actual ordered assignment/store sequence and expose its exact
continuation state, preserving the enlarged registry and all metadata. -/
theorem evaluate_stateFreshTx_constructor_sequence_fields {F : Type} (widths : BitVec 64 → BitVec 64)
    (specs : List (Nat × Nat × Nat)) :
    ∀ (state : PanSemStateFiniteExact 64 F) (pointer ts oldValue : BitVec 64) (tables : Set (BitVec 64)),
    StateFreshTxPlan widths pointer specs →
    (specs.map (fun spec => spec.2.2)).Nodup →
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
      state.clock ≤ post.clock + stateFreshTxClockBudget specs ∧ post.clock ≤ state.clock ∧
      (∀ address : BitVec 64, address.toNat < pointer.toNat →
        (∀ spec ∈ specs, address ≠ ts + BitVec.ofNat 64 spec.2.2) →
        post.memory address = state.memory address) ∧ StateFreshTxFields ts pointer specs post := by
  induction specs with
  | nil =>
    intro state pointer ts oldValue tables plan unique family apart code heap tsGlobal tLocal aligned header headers domain space ticks
    exact ⟨state,(fun _ => rfl),family,apart,headers,⟨oldValue,tLocal⟩,rfl,rfl,rfl,HeapGlobalsFrame.refl state,heap,by omega,by omega,(fun _ _ _ => rfl),(by intro binding member; cases member)⟩
  | cons spec rest ih =>
    obtain ⟨width,capacity,offset⟩ := spec
    intro state pointer ts oldValue tables plan unique family apart code heap tsGlobal tLocal aligned header headers domain space ticks
    obtain ⟨widthEq,widthBound,capacityBound,large,offsetBound,⟨bits,power⟩,restPlan⟩ := plan
    have capacityNat : (BitVec.ofNat 64 capacity).toNat = capacity := Nat.mod_eq_of_lt capacityBound
    have widthNat : (BitVec.ofNat 64 width).toNat = width := Nat.mod_eq_of_lt (by omega)
    have stepSpace : pointer.toNat + 81 * capacity + 114 ≤ 33806089496 := by
      change pointer.toNat + (81 * capacity + 114 + stateFreshTxAllocationBudget rest) ≤ _ at space
      omega
    have bounds := stateFreshTx_next_table_bounds pointer width capacity widthBound capacityBound stepSpace
    obtain ⟨middle,step,midFamily,midApart,midHeaders,midLocal,midStored,midCode,midDomain,midEndian,midGlobals,midHeap,cost,remaining,midFrame⟩ :=
      evaluate_stateFreshTx_constructor_store_memory_frame state widths tables (.const (BitVec.ofNat 64 width)) (.const (BitVec.ofNat 64 capacity))
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
    obtain ⟨post,tailRun,postFamily,postApart,postHeaders,postLocal,postCode,postDomain,postEndian,postGlobals,postHeap,tailCost,tailRemaining,tailFrame,tailFields⟩ :=
      ih middle (stateFreshTxNextTable pointer width capacity) ts pointer (insert pointer tables) restPlan (List.nodup_cons.mp unique).2 midFamily midApart
        (midCode.trans code) nextHeap ((midGlobals (ofString "ts") (by decide)).trans tsGlobal) midLocal bounds.2.2 (by omega)
        midHeaders nextDomain nextSpace nextTicks
    refine ⟨post,?_,postFamily,postApart,postHeaders,postLocal,postCode.trans midCode,postDomain.trans midDomain,
      postEndian.trans midEndian,midGlobals.trans postGlobals,postHeap,?_,by omega,?_,?_⟩
    · intro tail
      change evaluateHOLFiniteState state (.seq _ (.seq _ (stateFreshTxConstructorSequence rest tail))) = _
      rw [← evaluate_seq_assoc,evaluateHOLFiniteState_seq_line780]
      unfold stateFreshTxPointerStore
      rw [step]
      exact tailRun tail
    · change state.clock ≤ post.clock + (capacity + 8 + stateFreshTxClockBudget rest)
      rw [capacityNat] at cost
      omega
    · intro address before untouched
      have beforeNext : address.toNat < (stateFreshTxNextTable pointer width capacity).toNat := by omega
      have tailUntouched : ∀ spec ∈ rest, address ≠ ts + BitVec.ofNat 64 spec.2.2 := by
        intro spec member
        exact untouched spec (List.mem_cons_of_mem _ member)
      have headUntouched : address ≠ ts + BitVec.ofNat 64 offset :=
        untouched (width,capacity,offset) (by simp)
      exact (tailFrame address beforeNext tailUntouched).trans (midFrame address before headUntouched)
    · intro binding member
      rcases List.mem_cons.mp member with same | later
      · subst binding
        change post.memory (ts + BitVec.ofNat 64 offset) = .word pointer
        have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
        have slotNat : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
          rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
        have beforeNext : (ts + BitVec.ofNat 64 offset).toNat < (stateFreshTxNextTable pointer width capacity).toNat := by omega
        have untouched : ∀ spec ∈ rest, ts + BitVec.ofNat 64 offset ≠ ts + BitVec.ofNat 64 spec.2.2 := by
          intro spec member equal
          have small := StateFreshTxPlan.offset_bound widths rest _ restPlan spec member
          have natural : (BitVec.ofNat 64 spec.2.2).toNat = spec.2.2 := Nat.mod_eq_of_lt (by omega)
          have otherNat : (ts + BitVec.ofNat 64 spec.2.2).toNat = ts.toNat + spec.2.2 := by
            rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
          have same := congrArg BitVec.toNat equal
          rw [slotNat,otherNat] at same
          have equalOffset : offset = spec.2.2 := by omega
          have contains : offset ∈ rest.map (fun spec => spec.2.2) := by
            rw [equalOffset]
            exact List.mem_map_of_mem (f := fun spec => spec.2.2) member
          exact (List.nodup_cons.mp unique).1 contains
        rw [tailFrame _ beforeNext untouched]
        exact midStored
      · exact tailFields binding later

/-- The original transaction constructor stores each of its eight table pointers once. -/
theorem stateFreshTx_all_field_offsets_distinct :
    (stateFreshTxAllTables.map (fun spec => spec.2.2)).Nodup := by decide

theorem stateFreshTx_remaining_field_offsets_distinct :
    (stateFreshTxRemainingTables.map (fun spec => spec.2.2)).Nodup := by decide

#print axioms StateFreshTxPlan.offset_bound
#print axioms stateFreshTx_all_field_offsets_distinct
#print axioms stateFreshTx_remaining_field_offsets_distinct

#print axioms evaluate_stateFreshTx_constructor_sequence_fields
end InitECandidate.Runtime
