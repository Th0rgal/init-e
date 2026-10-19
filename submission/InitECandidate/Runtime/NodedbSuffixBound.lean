import InitECandidate.Runtime.NodedbLoopResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original index declaration, complete insertion loop and return are
bounded, including every unsuccessful outcome. -/
theorem runBounded_nodedb_suffix (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (heap : BitVec 64)
    (valid : NodedbLoopInv c 0 0 heap (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s))
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock) :
    RunBounded s (nodedbAt 3) (c.total.toNat * (nodedbIterationCost c.capacity c.total + 1)) := by
  rw [source_nodedb_insertion]
  apply RunBounded.decConst
  have loop := runBounded_nodedb_insertion_loop c g _ 0 heap valid budget
  have whole := RunBounded.seq (tail := .return (.var .local (ofString "t"))) (b := 0) loop (by change _ + 0 ≤ s.clock; omega) (by
    intro next normal nextCode remaining
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans valid.tableInv.code) remaining)
  simpa [setVarHOLFinite] using whole

#print axioms runBounded_nodedb_suffix
end InitECandidate.Runtime
