import InitECandidate.Runtime.HashTableValuesInSetCallAllPlans
import InitECandidate.Runtime.RollbackWorldRegisteredSetSavedValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteSavedValuesIn
import InitECandidate.Runtime.StateRestoreRecordDecisionPreservesJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual nonzero-presence undo-set branch preserves registered table values on normal resumption for every allocation plan. -/
theorem RollbackWorld.record_set_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key record present value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (restored : value ∈ targets) (zero : present ≠ 0)
    (success : (evaluateHOLFiniteState state stateRestoreRecordDecision).1 = none) :
    HashTableValuesIn table targets (evaluateHOLFiniteState state stateRestoreRecordDecision).2 := by
  classical
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,strideBound,capacityLarge⟩ := world.ready table member
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  have condition : @evalHOLExact 64 F _ state.toExact
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
  have selected : evaluateHOLFiniteState state stateRestoreRecordDecision =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)]) := by
    unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    rfl
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
    exact heapDomain address (by omega)
  have outcome := ready.set_call_all_plans_values_in state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
    targets registered restored strideBound ticks growthDomain _ _ _ args capacityLarge keyAligned keyWords keyBytes
  rcases outcome with good | failure
  · obtain ⟨post,run,_,postRegistered,_⟩ := good
    rw [selected,run]
    exact postRegistered
  · have callSuccess : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)])).1 = none := by
      rw [← selected]
      exact success
    exact False.elim (failure.1 callSuccess)

#print axioms RollbackWorld.record_set_values_in
end InitECandidate.Runtime
