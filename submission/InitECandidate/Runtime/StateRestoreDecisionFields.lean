import InitECandidate.Runtime.RollbackWorldRegisteredSetFields
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteFields
import InitECandidate.Runtime.StateRestoreRecordSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful undo decisions preserve all transaction fields and every global
except the heap frontier, for either saved presence value and all growth plans. -/
theorem RollbackWorld.record_decision_success_fields {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key record present value ts fieldPointer : BitVec 64) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 72 + 1 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (success : (evaluateHOLFiniteState state stateRestoreRecordDecision).1 = none) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables (evaluateHOLFiniteState state stateRestoreRecordDecision).2 ∧
      HeapGlobalsFrame state (evaluateHOLFiniteState state stateRestoreRecordDecision).2 := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  by_cases zero : present = 0
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,zero]
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision = evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_del") [.var .local (ofString "t"),.var .local (ofString "key")]) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      rfl
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
    obtain ⟨post,run,_,_,_,_,globals,postFields⟩ := world.registered_delete_bounded_fields state widths tables journal snapshot count table key separated member supported
      ts fieldPointer fields headerBefore (by omega) _ _ args keyAligned keyWords keyBytes
    rw [selected,run]
    exact ⟨postFields,HeapGlobalsFrame.of_globals globals⟩
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      rw [evalHOLExact,loaded]
      simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    have loadedValue : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (hashLocalAddress (ofString "r") 24)) = some (.val (.word value)) := by
      simp only [evalHOLExact,isWfShapeExactHOL]
      rw [eval_hashLocalAddress state (ofString "r") record 24 r]
      simp [memLoadHOLExact]
      exact ⟨valueDomain,valueCell⟩
    have selected : evaluateHOLFiniteState state stateRestoreRecordDecision = evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_set") [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)]) := by
      unfold stateRestoreRecordDecision
      rw [evaluateHOLFiniteState_ite,condition]
      rfl
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)] =
        some [.val (.word table),.val (.word key),.val (.word value)] := by
      simp only [evalListHOLFinite,evalListHOLExact]
      rw [loadedValue]
      simp [evalHOLExact,t,k]
    have normal := (congrArg Prod.fst selected).symm.trans success
    have postFields := world.registered_set_success_fields state widths tables journal snapshot count table key value separated member supported
      ts fieldPointer fields headerBefore ticks heapDomain _ _ _ args keyAligned keyWords keyBytes normal
    have globals := world.registered_set_success_heap_frame state widths tables journal snapshot count table key value separated member supported
      ticks heapDomain _ _ _ args keyAligned keyWords keyBytes normal
    rw [selected]
    exact ⟨postFields,globals⟩

#print axioms RollbackWorld.record_decision_success_fields
end InitECandidate.Runtime
