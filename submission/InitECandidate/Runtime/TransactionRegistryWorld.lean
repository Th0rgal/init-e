import InitECandidate.Runtime.TransactionRuntimeWorld
import InitECandidate.Runtime.RollbackWorldJournalSetCallFields
import InitECandidate.Runtime.RollbackWorldJournalDeleteCallFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Recurrent transaction state allowing dynamically allocated storage tables
in addition to the eight tables referenced by transaction header fields. -/
structure TransactionRegistryWorld {F : Type} (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  journalWorld : JournalRuntimeWorld widths tables journal snapshot count state
  fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state
  tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts))
  tsBound : ts.toNat + 72 ≤ 33806089496
  journalBeforeTs : journal.toNat + 524288 * 32 ≤ ts.toNat
  fieldRegistry : stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅ ⊆ tables
  tableHeaders : ∀ table ∈ tables, ts.toNat + 72 ≤ table.toNat

/-- The initialized fixed registry is a valid starting point for later registry growth. -/
theorem TransactionRuntimeWorld.to_registry {F : Type}
    {widths : BitVec 64 → BitVec 64} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state) :
    TransactionRegistryWorld widths (stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅)
      fieldPointer ts journal snapshot count state :=
  ⟨valid.journalWorld,valid.fields,valid.tsGlobal,valid.tsBound,valid.journalBeforeTs,(fun _ member => member),valid.tableHeaders⟩

/-- Loading an initialized source field selects a registered table, with field
accessibility derived from the recurrent heap domain. -/
theorem TransactionRegistryWorld.load_registered {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (fieldPointer ts journal snapshot count : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) = some (.val (.word table)) ∧
      table ∈ tables := by
  have loaded := valid.fields.load_registered_full_heap state ts fieldPointer ∅ offset table binding valid.tsGlobal valid.tsBound valid.journalWorld.heapDomain
  exact ⟨loaded.1,valid.fieldRegistry loaded.2⟩

/-- The original jset call retains the complete transaction invariant on success. -/
theorem TransactionRegistryWorld.jset_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (fieldPointer ts journal snapshot count table key value : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 73 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) output.2) := by
  have contract := valid.journalWorld.jset_call state widths tables journal snapshot count table key value member tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks
  refine ⟨contract.1,contract.2.1,contract.2.2.1,?_⟩
  intro success
  have fields := rollback_world_jset_call_success_fields state widths tables journal snapshot count table key value
    valid.journalWorld.world valid.journalWorld.separated member (valid.journalWorld.supported table member)
    tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks valid.journalWorld.journalBound valid.journalWorld.journalAligned
    valid.journalWorld.journalHeaders valid.journalWorld.heapDomain valid.journalWorld.capacity
    ts fieldPointer valid.fields valid.tsBound valid.journalBeforeTs (valid.tableHeaders table member) valid.journalWorld.code success
  have globals := rollback_world_jset_call_success_globals state widths tables journal snapshot count table key value
    valid.journalWorld.world valid.journalWorld.separated member (valid.journalWorld.supported table member)
    tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks valid.journalWorld.journalBound valid.journalWorld.journalAligned
    valid.journalWorld.journalHeaders valid.journalWorld.heapDomain valid.journalWorld.capacity valid.journalWorld.code success
  exact ⟨contract.2.2.2 success,fields,(globals (ofString "ts") (by decide) (by decide)).trans valid.tsGlobal,
    valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩

#print axioms TransactionRegistryWorld.jset_call

/-- The original jdel call retains the complete transaction invariant on success. -/
theorem TransactionRegistryWorld.jdel_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧ TransactionRegistryWorld widths tables fieldPointer ts journal snapshot next output.2) := by
  have contract := valid.journalWorld.jdel_call state widths tables journal snapshot count table key member tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks
  refine ⟨contract.1,contract.2.1,contract.2.2.1,?_⟩
  intro success
  have fields := rollback_world_jdel_call_success_fields state widths tables journal snapshot count table key
    valid.journalWorld.world valid.journalWorld.separated member (valid.journalWorld.supported table member)
    tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks valid.journalWorld.journalBound valid.journalWorld.journalAligned
    valid.journalWorld.journalHeaders valid.journalWorld.heapDomain valid.journalWorld.capacity
    ts fieldPointer valid.fields valid.tsBound valid.journalBeforeTs (valid.tableHeaders table member) valid.journalWorld.code success
  have globals := rollback_world_jdel_call_success_globals state widths tables journal snapshot count table key
    valid.journalWorld.world valid.journalWorld.separated member (valid.journalWorld.supported table member)
    tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks valid.journalWorld.journalBound valid.journalWorld.journalAligned
    valid.journalWorld.journalHeaders valid.journalWorld.heapDomain valid.journalWorld.capacity valid.journalWorld.code success
  obtain ⟨next,counts,world⟩ := contract.2.2.2 success
  exact ⟨next,counts,world,fields,(globals (ofString "ts") (by decide) (by decide)).trans valid.tsGlobal,
    valid.tsBound,valid.journalBeforeTs,valid.fieldRegistry,valid.tableHeaders⟩

#print axioms TransactionRegistryWorld.jdel_call

#print axioms TransactionRuntimeWorld.to_registry
#print axioms TransactionRegistryWorld.load_registered
end InitECandidate.Runtime
