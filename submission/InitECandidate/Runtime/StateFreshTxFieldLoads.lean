import InitECandidate.Runtime.StateFreshTxTableBindings
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact initialized transaction-state table-pointer fields. -/
def StateFreshTxFields {F : Type} (ts pointer : BitVec 64) (specs : List (Nat × Nat × Nat))
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ binding ∈ stateFreshTxTableBindings pointer specs,
    state.memory (ts + BitVec.ofNat 64 binding.1) = .word binding.2

/-- Actual source field loading selects a member of the constructed registry. -/
theorem StateFreshTxFields.load_registered {F : Type} (state : PanSemStateFiniteExact 64 F)
    (ts pointer : BitVec 64) (specs : List (Nat × Nat × Nat)) (tables : Set (BitVec 64))
    (fields : StateFreshTxFields ts pointer specs state) (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings pointer specs)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (domain : state.memaddrs (ts + BitVec.ofNat 64 offset)) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) = some (.val (.word table)) ∧
      table ∈ stateFreshTxRegistryAfter pointer specs tables := by
  have cell := fields (offset,table) binding
  refine ⟨?_,stateFreshTx_binding_registered specs pointer tables (offset,table) binding⟩
  simp [evalHOLExact,evalListHOLExact,tsGlobal,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,isWfShapeExactHOL,domain,cell]

/-- Caller-local changes and non-memory metadata cannot change initialized fields. -/
theorem StateFreshTxFields.after_memory {F : Type} {ts pointer : BitVec 64} {specs : List (Nat × Nat × Nat)}
    {before after : PanSemStateFiniteExact 64 F} (fields : StateFreshTxFields ts pointer specs before)
    (memory : after.memory = before.memory) : StateFreshTxFields ts pointer specs after := by
  intro binding member
  rw [memory]
  exact fields binding member

/-- The actual eight fields are accessible from the allocated TS header and
full heap domain; no individual field-domain premise is required. -/
theorem StateFreshTxFields.load_registered_full_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (ts pointer : BitVec 64) (tables : Set (BitVec 64))
    (fields : StateFreshTxFields ts pointer stateFreshTxAllTables state) (offset : Nat) (table : BitVec 64)
    (binding : (offset,table) ∈ stateFreshTxTableBindings pointer stateFreshTxAllTables)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (tsBound : ts.toNat + 72 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) = some (.val (.word table)) ∧
      table ∈ stateFreshTxRegistryAfter pointer stateFreshTxAllTables tables := by
  have offsets := List.mem_map_of_mem (f := Prod.fst) binding
  rw [stateFreshTx_table_binding_offsets] at offsets
  have small : offset < 72 := by simp at offsets; omega
  have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  exact fields.load_registered state ts pointer stateFreshTxAllTables tables offset table binding tsGlobal (heapDomain _ (by omega))

#print axioms StateFreshTxFields.load_registered_full_heap
#print axioms StateFreshTxFields.load_registered
#print axioms StateFreshTxFields.after_memory
end InitECandidate.Runtime
