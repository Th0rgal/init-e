import InitECandidate.Runtime.RollbackWorldRegisteredDeleteValuesInFamily
import InitECandidate.Runtime.RollbackWorldRecordSetValuesInFamily
import InitECandidate.Runtime.RollbackWorldRegisteredSetSavedValuesIn
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteSavedValuesIn
import InitECandidate.Runtime.StateRestoreRecordDecisionPreservesJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both actual undo branches preserve every watched table on normal resumption. -/
theorem RollbackWorld.record_decision_values_in_family {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key record present value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
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
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (restored : present ≠ 0 → table ∈ watched → value ∈ targets)
    (success : (evaluateHOLFiniteState state stateRestoreRecordDecision).1 = none) :
    ∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state stateRestoreRecordDecision).2 := by
  classical
  by_cases zero : present = 0
  · have loaded : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
      simp only [evalHOLExact,isWfShapeExactHOL]
      rw [eval_hashLocalAddress state (ofString "r") record 16 r]
      simp [memLoadHOLExact]
      exact ⟨presentDomain,presentCell⟩
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,zero]
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
    have family := world.registered_delete_values_in_family state widths tables journal snapshot count table key separated member supported (by omega)
      _ _ args keyAligned keyWords keyBytes watched targets watchedSubset registered
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision =
        evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del")
          [.var .local (ofString "t"),.var .local (ofString "key")]) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      rfl
    rw [selected]
    exact family
  · exact world.record_set_values_in_family state widths tables journal snapshot count table key record present value separated member supported ticks heapDomain
      t k r presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes watched targets watchedSubset registered (restored zero) zero success

#print axioms RollbackWorld.record_decision_values_in_family
end InitECandidate.Runtime
