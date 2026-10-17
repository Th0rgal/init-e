import InitECandidate.Runtime.JournalRuntimeWorld
import InitECandidate.Runtime.RollbackWorldJournalSetCallFields
import InitECandidate.Runtime.RollbackWorldJournalDeleteCallFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Recurrent transaction state: the journal, all eight concrete table fields,
and the fixed separation of their header from journal records and tables. -/
structure TransactionRuntimeWorld {F : Type} (widths : BitVec 64 → BitVec 64)
    (fieldPointer ts journal snapshot count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  journalWorld : JournalRuntimeWorld widths (stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅) journal snapshot count state
  fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state
  tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts))
  tsBound : ts.toNat + 72 ≤ 33806089496
  journalBeforeTs : journal.toNat + 524288 * 32 ≤ ts.toNat
  tableHeaders : ∀ table ∈ stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅, ts.toNat + 72 ≤ table.toNat

/-- Loading an initialized source field selects a registered table, with field
accessibility derived from the recurrent heap domain. -/
theorem TransactionRuntimeWorld.load_registered {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) = some (.val (.word table)) ∧
      table ∈ stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅ :=
  valid.fields.load_registered_full_heap state ts fieldPointer ∅ offset table binding valid.tsGlobal valid.tsBound valid.journalWorld.heapDomain

/-- The original jset call retains the complete transaction invariant on success. -/
theorem TransactionRuntimeWorld.jset_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count table key value : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (member : table ∈ stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 73 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRuntimeWorld widths fieldPointer ts journal snapshot (count + 1) output.2) := by
  let tables := stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅
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
    valid.tsBound,valid.journalBeforeTs,valid.tableHeaders⟩

#print axioms TransactionRuntimeWorld.jset_call

/-- The original jdel call retains the complete transaction invariant on success. -/
theorem TransactionRuntimeWorld.jdel_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (member : table ∈ stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧ TransactionRuntimeWorld widths fieldPointer ts journal snapshot next output.2) := by
  let tables := stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅
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
    valid.tsBound,valid.journalBeforeTs,valid.tableHeaders⟩

#print axioms TransactionRuntimeWorld.jdel_call

#print axioms TransactionRuntimeWorld.load_registered
end InitECandidate.Runtime
