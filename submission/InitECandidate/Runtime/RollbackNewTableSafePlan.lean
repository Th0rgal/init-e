import InitECandidate.Runtime.HashNewReadySafePlan
import InitECandidate.Runtime.HashNewBeforeHeaderSafePlan
import InitECandidate.Runtime.RollbackNewTableRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful actual constructor plan retains every old table by preserving
its physical footprint below the old heap frontier. -/
theorem evaluate_htabNew_ready_frame_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      (∀ (oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems : BitVec 64) (oldBits : Nat),
        HashTableReady oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits table state →
        HashTableReady oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits
          (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)) ready) ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      HashTableReady keyLength table (allocationEnd table 72) (allocationEnd 0 keyLength) capacity
        (htabNewUsed table keyLength capacity) (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
        (htabNewOrderPos table keyLength capacity) 0 bits
        (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)) ready ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  obtain ⟨ready,run,empty,cost,remaining,locals,postCode,domain,endian,newReady,decl⟩ :=
    evaluate_htabNew_ready_of_safe_plan state keyArgument capacityArgument table keyLength capacity bits arguments power tableDomain code ticks heap
      keyBound tableAligned pointerBound fullSafe headerDomain wordDomain byteDomain
  refine ⟨ready,run,empty,?_,cost,remaining,locals,postCode,domain,endian,newReady,decl⟩
  intro oldKeyLength oldTable oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits oldReady
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,memory,_⟩ :=
    evaluate_htabNew_call_and_declaration_before_header_of_safe_plan state keyArgument capacityArgument table keyLength capacity
      arguments code ticks heap pointerBound tableAligned fullSafe headerDomain wordDomain byteDomain
  have same : ready = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  have beforeMemory : ∀ address : BitVec 64, address.toNat < table.toNat → ready.memory address = state.memory address := by
    rw [same]; exact memory
  have frontier := htabNew_frontier_facts_of_safe_plan table keyLength capacity pointerBound fullSafe
  have monotone : table.toNat ≤ (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)).toNat := by
    have layout := htabNew_insertion_layout_of_safe_plan table keyLength capacity pointerBound fullSafe
    dsimp only at layout
    omega
  apply oldReady.physical_frame_advance state ready oldKeyLength oldTable table
    (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)) oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits
  · intro address member
    exact beforeMemory address (oldReady.physical_below_frontier state oldKeyLength oldTable table oldKeys oldStride oldCapacity oldUsed oldValues oldOrder oldOrderPos oldItems oldBits address member)
  · exact newReady.live.frontier.heap
  · exact monotone
  · exact frontier.2.1
  · exact frontier.2.2
  · exact postCode
  · exact domain
  · exact endian


/-- A successful actual allocation plan extends the separated table registry,
including successes with less than the old conservative heap reserve. -/
theorem rollback_htabNew_registry_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (keyArgument capacityArgument : ExpHOL 64) (table capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word (widths table)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table (widths table) capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : (widths table).toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes (widths table) capacity))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table (widths table) capacity + BitVec.ofNat 64 offset)))
    (large : 1 < capacity.toNat)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,post) ∧
      (∀ other ∈ insert table tables, RollbackTableReady widths other post) ∧
      RollbackPhysicalSeparated widths (insert table tables) post ∧
      state.clock ≤ post.clock + capacity.toNat + 8 ∧ post.clock ≤ state.clock := by
  obtain ⟨post,run,_,retained,cost,remaining,_,_,_,_,newReady,_⟩ := evaluate_htabNew_ready_frame_of_safe_plan state
    keyArgument capacityArgument table (widths table) capacity bits arguments power tableDomain code ticks heap keyBound tableAligned pointerBound fullSafe headerDomain wordDomain byteDomain
  have oldReady : ∀ other ∈ tables, ∃ op ok os oc ou ov oo oop oi ob,
      HashTableReady (widths other) other ok os oc ou ov oo oop oi ob table state ∧
      HashTableReady (widths other) other ok os oc ou ov oo oop oi ob op post ∧ os.toNat ≤ 56 ∧ 1 < oc.toNat := by
    intro other member
    obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,valid,small,big⟩ := family other member
    have equal : op = table := by
      have eq := valid.live.frontier.heap.symm.trans heap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using eq
    subst op
    exact ⟨_,ok,os,oc,ou,ov,oo,oop,oi,ob,valid,retained (widths other) other ok os oc ou ov oo oop oi ob valid,small,big⟩
  have subset : ∀ other ∈ tables, ∀ address, rollbackTableFootprint widths other post address → rollbackTableFootprint widths other state address := by
    intro other member address inside
    obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,old,kept,_,_⟩ := oldReady other member
    exact (old.rollback_footprint_iff state widths other table ok os oc ou ov oo oop oi ob address).mpr
      ((kept.rollback_footprint_iff post widths other op ok os oc ou ov oo oop oi ob address).mp inside)
  have newAfter : ∀ address, rollbackTableFootprint widths table post address → table.toNat ≤ address.toNat := by
    intro address inside
    have member := (newReady.rollback_footprint_iff post widths table _ _ _ _ _ _ _ _ _ _ address).mp inside
    have hk := newReady.live.arrays.headerKeys
    have hv := newReady.live.arrays.headerValues
    have ku := newReady.live.arrays.keysBefore
    have uo := newReady.live.arrays.usedBefore
    have oo := newReady.live.arrays.orderBefore
    unfold tablePhysicalRegion at member
    omega
  have cross : ∀ other ∈ tables, ∀ address, rollbackTableFootprint widths table post address → ¬rollbackTableFootprint widths other post address := by
    intro other member address newInside oldInside
    obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,old,kept,_,_⟩ := oldReady other member
    have oldMember := (old.rollback_footprint_iff state widths other table ok os oc ou ov oo oop oi ob address).mp (subset other member address oldInside)
    have below := old.physical_below_frontier state (widths other) other table ok os oc ou ov oo oop oi ob address oldMember
    have above := newAfter address newInside
    omega
  refine ⟨post,run,?_,?_,cost,remaining⟩
  · intro other member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst other
      exact ⟨_,_,_,_,_,_,_,_,_,_,newReady,(htabNew_stride_bound (widths table) keyBound).2.1,large⟩
    · obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,_,kept,small,big⟩ := oldReady other old
      exact ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,kept,small,big⟩
  · intro first firstMember second secondMember different address firstInside secondInside
    rcases Set.mem_insert_iff.mp firstMember with firstNew | firstOld
    · subst first
      rcases Set.mem_insert_iff.mp secondMember with secondNew | secondOld
      · exact different secondNew.symm
      · exact cross second secondOld address firstInside secondInside
    · rcases Set.mem_insert_iff.mp secondMember with secondNew | secondOld
      · subst second
        exact cross first firstOld address secondInside firstInside
      · exact separated first firstOld second secondOld different address (subset first firstOld address firstInside) (subset second secondOld address secondInside)

#print axioms evaluate_htabNew_ready_frame_of_safe_plan
#print axioms rollback_htabNew_registry_of_safe_plan
end InitECandidate.Runtime
