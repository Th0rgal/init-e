import InitECandidate.Runtime.DiscardCallNoBreak
import InitECandidate.Runtime.RollbackWorldSetAllPlans
import InitECandidate.Runtime.RollbackWorldDeleteSeparated
import InitECandidate.Runtime.StateRestoreRecordDecisionPreservesJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual undo decision preserves the complete world and physical
separation, choosing set or delete from the saved presence field. -/
theorem RollbackWorld.record_decision_all_plans_no_break {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key record present value : BitVec 64) (bits : Nat)
    (supported : (widths table) = 20 ∨ (widths table) = 32 ∨ (widths table) = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (setBudget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (deleteBudget : capacity.toNat * 57 + 3 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : RollbackPhysicalSeparated widths tables state) :
    (∃ post, evaluateHOLFiniteState state stateRestoreRecordDecision = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post) ∨
    ((evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ none ∧
      (evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ some .timeOut ∧
      (∀ output : ValueHOL 64, (evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ some (.returned output)) ∧
      (evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ some .continue ∧
      (evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ some .break) := by
  classical
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  by_cases zero : present = 0
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,zero]
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
    obtain ⟨post,run,preserved,apart,_,_⟩ := RollbackWorld.delete_call_preserves_separation state widths tables
      table pointer keys stride capacity used values order orderPos items key bits supported ready strideBound capacityLarge
      _ _ args keyAligned keyWords keyBytes deleteBudget journal snapshot count world registered separated
    refine Or.inl ⟨post,?_,preserved,apart⟩
    unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    simpa using run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    have loadedValue : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (hashLocalAddress (ofString "r") 24)) = some (.val (.word value)) := by
      simp only [evalHOLExact,isWfShapeExactHOL]
      rw [eval_hashLocalAddress state (ofString "r") record 24 r]
      simp [memLoadHOLExact]
      exact ⟨valueDomain,valueCell⟩
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)] = some [.val (.word table),.val (.word key),.val (.word value)] := by
      simp only [evalListHOLFinite,evalListHOLExact]
      rw [loadedValue]
      simp [evalHOLExact,t,k]
    have capacityBound : capacity.toNat ≤ 33806089496 := by
      have := ready.live.arrays.usedBefore
      have := ready.live.arrays.orderBefore
      have := ready.live.arrays.endBound
      omega
    have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
      have := ready.live.arrays.headerKeys
      have := ready.live.arrays.keysBefore
      have := ready.live.arrays.usedBefore
      have := ready.live.arrays.orderBefore
      have := ready.live.frontier.allocated
      omega
    have growthDomain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) →
        ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
      intro safePlan address lower upper
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride strideBound ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
      exact domain address lower (by omega)
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision =
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
          [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)]) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      rfl
    have outcome := RollbackWorld.set_call_all_plans state widths tables
      table pointer keys stride capacity used values order orderPos items key value bits supported ready strideBound capacityLarge
      setBudget growthDomain _ _ _ args keyAligned keyWords keyBytes journal snapshot count world registered separated
    rcases outcome with success | failure
    · obtain ⟨post,run,preserved,apart⟩ := success
      exact Or.inl ⟨post,selected.trans run,preserved,apart⟩
    · obtain ⟨terminal,noTimeout,noReturn,noContinue,_,_⟩ := failure
      rw [selected]
      exact Or.inr ⟨terminal,noTimeout,noReturn,noContinue,evaluate_discard_call_no_break state _ _⟩

#print axioms RollbackWorld.record_decision_all_plans_no_break
end InitECandidate.Runtime
