import InitECandidate.Runtime.PtWsFloorGD
import InitECandidate.Runtime.StateFreshTxRegistryLowerBound
/-!
The table-header floor: every transaction table constructed by the actual `state_fresh_tx` from an allocation pointer at
or above a floor lies at or above it (root's `stateFreshTx_registry_lower_bound`), so with the floor at the final
initializer heap the repaired table premises hold for the tables at `ts + 16` and `ts + 32` (`koWsL_floor`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem stateFreshTx_binding_floor (pointer : BitVec 64) (L0 : Nat) (hp : L0 ≤ pointer.toNat)
    (budget : pointer.toNat + stateFreshTxAllocationBudget stateFreshTxAllTables ≤ 33806089496)
    (binding : Nat × BitVec 64) (mem : binding ∈ stateFreshTxTableBindings pointer stateFreshTxAllTables) :
    L0 ≤ binding.2.toNat :=
  stateFreshTx_registry_lower_bound stateFreshTxAllTables pointer ∅ L0 stateFreshTx_all_literals hp
    (fun _ h => False.elim h) budget binding.2 (stateFreshTx_binding_registered _ _ _ _ mem)

/-- The repaired premises for a table field of the actual transaction state, from the final initializer floor. -/
theorem koWsL_of_freshTx {SP0 FM pointer : BitVec 64} (hSP : SP0.toNat ≤ 2713714688)
    (hp : 2713731432 ≤ pointer.toNat)
    (budget : pointer.toNat + stateFreshTxAllocationBudget stateFreshTxAllTables ≤ 33806089496)
    (offset : Nat) (Tt : BitVec 64) (mem : (offset,Tt) ∈ stateFreshTxTableBindings pointer stateFreshTxAllTables) :
    KoWsL SP0 FM 2713714976#64 2713715176#64 2713717520#64 Tt ∧ TabAvoid (fun x => ¬ MWin 2713718280#64 448 x) Tt :=
  ⟨koWsL_floor hSP (stateFreshTx_binding_floor pointer _ hp budget _ mem),
    koSc_floor (stateFreshTx_binding_floor pointer _ hp budget _ mem)⟩

#print axioms stateFreshTx_binding_floor
#print axioms koWsL_of_freshTx
end InitECandidate.Runtime
