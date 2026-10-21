import InitECandidate.Runtime.SourceCostPanSimpCode
import InitECandidate.Runtime.SourceCostSharpSource
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem SimpWorkLe.sharpScore {a b : List WorkEvent} (le : SimpWorkLe a b) :
    sharpScore a ≤ sharpScore b := by
  have w := le.score sharpSourceWeights
  simp only [sharpScore, sharpSourceScore]
  exact w

/-- `pan_simp` with its installed code map never increases the sharp score. -/
theorem simp_compile_run_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64} {r ev}
    (run : StatementRun fn s p r post ev) (ok : r ≠ some .error)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hc : PanSimp.CodeRel s.code c) :
    ∃ ev', StatementRun fn { s with code := c } (panSimpCompileHOL p) r { post with code := c } ev' ∧
      sharpScore ev' ≤ sharpScore ev := by
  obtain ⟨ev', run', le⟩ := simp_compile_run run ok c hc
  exact ⟨ev', run', le.sharpScore⟩

#print axioms SimpWorkLe.sharpScore
#print axioms simp_compile_run_sharp
end InitECandidate.Runtime.FineCost
