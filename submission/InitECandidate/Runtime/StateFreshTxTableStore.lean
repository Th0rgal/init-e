import InitECandidate.Runtime.RollbackRegistryStores
import InitECandidate.Runtime.HashNewHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual transaction-state pointer store lies in the 72-byte header before
the transaction tables, so it retains the enlarged mixed-width registry. -/
theorem evaluate_stateFreshTx_table_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (ts value : BitVec 64) (offset : Nat)
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word ts)))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word value)))
    (small : offset < 72) (bounded : ts.toNat + 72 ≤ 33806089496)
    (domain : state.memaddrs (ts + BitVec.ofNat 64 offset))
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (afterHeader : ∀ table ∈ tables, ts.toNat + 72 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.store (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))) = (none,post) ∧
      (∀ table ∈ tables, RollbackTableReady widths table post) ∧ RollbackPhysicalSeparated widths tables post ∧
      post.memory (ts + BitVec.ofNat 64 offset) = .word value ∧ post.clock = state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs := by
  have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
    have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
  have preserved := rollback_registry_after_word state widths tables (ts + BitVec.ofNat 64 offset) value family separated (by
    intro table member inside
    have lower := rollback_footprint_above_header inside
    have above := afterHeader table member
    omega)
  have evaluated : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)]) = some (.val (.word (ts + BitVec.ofNat 64 offset))) := by
    simp [evalHOLExact,evalListHOLExact,tsGlobal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  refine ⟨sourceWriteWord state (ts + BitVec.ofNat 64 offset) value,
    evaluate_store_word state _ value _ _ evaluated tableLocal domain,preserved.1,preserved.2,?_,rfl,rfl,rfl,rfl,rfl⟩
  simp [sourceWriteWord]

#print axioms evaluate_stateFreshTx_table_store
end InitECandidate.Runtime
