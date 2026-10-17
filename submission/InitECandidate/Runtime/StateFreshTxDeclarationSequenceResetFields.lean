import InitECandidate.Runtime.StateFreshTxConstructorDeclarationStore
import InitECandidate.Runtime.StateFreshTxSequenceResetFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose the scoped first constructor, remaining constructors, and journal reset. -/
theorem evaluate_stateFreshTx_declaration_sequence_reset_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (keyArgument capacityArgument : ExpHOL 64) (table capacity : BitVec 64) (bits : Nat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word (widths table)),.val (.word capacity)])
    (power : capacity.toNat = 2 ^ bits)
    (code : state.code = originalRuntimeCode) (specs : List (Nat × Nat × Nat))
    (ticks : capacity.toNat + 8 + stateFreshTxClockBudget specs ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : (widths table).toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 + stateFreshTxAllocationBudget specs ≤ 33806089496)
    (large : 1 < capacity.toNat)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (ts : BitVec 64) (offset : Nat)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (offsetBound : offset < 72)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (oldHeaders : ∀ other ∈ tables, ts.toNat + 72 ≤ other.toNat)
    (plan : StateFreshTxPlan widths (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)) specs)
    (unique : (specs.map (fun spec => spec.2.2)).Nodup)
    (firstUnique : offset ∉ specs.map (fun spec => spec.2.2))
    (journal snapshot oldCount : BitVec 64)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (journalBefore : journal.toNat ≤ ts.toNat + 72) :
    ∃ post, evaluateHOLFiniteState state
      (.decCall (ofString "t") .one (ofString "htab_new") [keyArgument,capacityArgument]
        (.seq (.store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t")))
          (stateFreshTxConstructorSequence specs (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0)))))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),
        {emptyLocalsHOLFinite post with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite post).locals (ofString "t",state.locals.lookup (ofString "t"))}) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)) specs (insert table tables))
        journal snapshot 0 (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)) specs (insert table tables)) post ∧
      state.clock ≤ post.clock + capacity.toNat + 8 + stateFreshTxClockBudget specs ∧
      post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧ post.code = state.code ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) ∧
      post.memory (ts + BitVec.ofNat 64 offset) = .word table ∧
      StateFreshTxFields ts (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)) specs post := by
  have firstBudget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496 := by omega
  obtain ⟨middle,run,registry,apart,headers,tLocal,firstStored,midCode,midDomain,midEndian,globals,heapNext,cost,remaining⟩ :=
    evaluate_stateFreshTx_constructor_declaration_store state widths tables keyArgument capacityArgument table capacity bits arguments power code
      (by omega) heap keyBound tableAligned firstBudget large family separated ts offset tsGlobal offsetBound heapDomain headerBefore oldHeaders
  have frontier := htabNew_frontier_facts table (widths table) capacity keyBound firstBudget
  have space := htabNew_allocation_plan_safe table (widths table) capacity keyBound firstBudget
  have upper : (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)).toNat ≤ table.toNat + 81 * capacity.toNat + 114 := by
    simpa only [htabNewOrderPos,htabNewOrder,htabNewUsed,htabNewValues,htabNewAllocationSizes,allocationPlanEnd] using space.2
  obtain ⟨_,_,_,_,beforeValues,valuesBefore,usedBefore,orderBefore,endBound⟩ := htabNew_insertion_layout table (widths table) capacity keyBound firstBudget
  obtain ⟨post,finish,world,postApart,postCost,postRemaining,postDomain,postCode,postEndian,postGlobals,fields,memoryFrame⟩ :=
    evaluate_stateFreshTx_sequence_reset_fields widths specs middle _ ts table (insert table tables) journal snapshot oldCount plan unique registry apart
      (midCode.trans code) heapNext ((globals (ofString "ts") (by decide)).trans tsGlobal) tLocal frontier.2.2
      (by omega) headers (by intro address bound; rw [midDomain]; exact heapDomain address bound)
      (by omega) (by omega) ((globals (ofString "journal") (by decide)).trans journalGlobal)
      ((globals (ofString "journal_n") (by decide)).trans counterGlobal) journalBefore
  refine ⟨post,?_,world,postApart,by omega,by omega,postDomain.trans midDomain,postCode.trans midCode,postEndian.trans midEndian,?_,?_,fields⟩
  · rw [run,finish]
  · intro name notHeap notCounter
    exact (postGlobals name notHeap notCounter).trans (globals name notHeap)
  · have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have slotNat : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
    have before : (ts + BitVec.ofNat 64 offset).toNat <
        (allocationEnd (htabNewOrderPos table (widths table) capacity) (capacity * 8)).toNat := by omega
    have untouched : ∀ spec ∈ specs, ts + BitVec.ofNat 64 offset ≠ ts + BitVec.ofNat 64 spec.2.2 := by
      intro spec member equal
      have small := StateFreshTxPlan.offset_bound widths specs _ plan spec member
      have natural : (BitVec.ofNat 64 spec.2.2).toNat = spec.2.2 := Nat.mod_eq_of_lt (by omega)
      have otherNat : (ts + BitVec.ofNat 64 spec.2.2).toNat = ts.toNat + spec.2.2 := by
        rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
      have same := congrArg BitVec.toNat equal
      rw [slotNat,otherNat] at same
      have equalOffset : offset = spec.2.2 := by omega
      apply firstUnique
      rw [equalOffset]
      exact List.mem_map_of_mem (f := fun spec => spec.2.2) member
    rw [memoryFrame _ before untouched]
    exact firstStored

#print axioms evaluate_stateFreshTx_declaration_sequence_reset_fields
end InitECandidate.Runtime
