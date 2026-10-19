import InitECandidate.Runtime.RunAttemptTwoDatabaseTablesReach
import InitECandidate.Runtime.HtabReadOnly
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def nodedbGetCost : Nat := 14 + 536870912 * 130

/-- An actual built table supplies the free-slot premise for the original hash
lookup. Failed key reads are covered as terminating outcomes by the lookup proof. -/
theorem runBounded_nodedb_table_get {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total key : BitVec 64) (built : NodedbTableAt s table heap total)
    (atTable : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (atKey : s.locals.lookup (ofString "key") = some (.val (.word key)))
    (budget : nodedbGetCost ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_htab_get) nodedbGetCost := by
  obtain ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,countBound,capBound,room,inv,ordered,extent⟩ := built
  have cost : (32#64).toNat / 8 + 8 + 1 + (capacity.toNat * (4 * (32#64).toNat + 1 + 0 + 1) + 0) + 1 + 0 ≤
      nodedbGetCost := by
    change 13 + (capacity.toNat * 130 + 0) + 1 + 0 ≤ _
    unfold nodedbGetCost
    omega
  exact (evaluate_htabGet_body_bounded s 32 table keys stride capacity used values order orderPos count key bits
    inv atTable atKey room (by decide) (cost.trans budget)).weaken cost

#print axioms runBounded_nodedb_table_get
end InitECandidate.Runtime
