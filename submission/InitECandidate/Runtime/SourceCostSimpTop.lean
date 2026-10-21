import InitECandidate.Runtime.SourceCostSharpPanSimp
import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! Top-level `pan_simp`: declarations of the simplified program install the
simplified bodies; the entry call from the installed state costs no more. -/

theorem simp_top_entry {F : Type} (decls : List (DeclHOL 64)) (s : PanSemStateFiniteExact 64 F)
    (emptyCode : s.code = HolFiniteMapExact.empty) {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @evaluateDeclsHOLFinite 64 F _ { s with structs := [] }
      (fun a => Classical.propDecidable (s.memaddrs a)) decls = some s1)
    (start : MlS) (clock : Nat) {r post ev}
    (run : StatementRun fn { s1 with clock := clock } (.call none start []) r post ev)
    (ok : r ≠ some .error) :
    ∃ s1', @evaluateDeclsHOLFinite 64 F _ { s with structs := [] }
        (fun a => Classical.propDecidable (s.memaddrs a)) (panSimpDeclsHOL decls) = some s1' ∧
      ∃ post' ev', StatementRun fn { s1' with clock := clock } (.call none start []) r post' ev' ∧
        sharpScore ev' ≤ sharpScore ev := by
  have rel : PanSimp.CodeRel ({ s with structs := [] } : PanSemStateFiniteExact 64 F).code s.code := by
    refine ⟨fun f h => h, ?_⟩
    intro f vshs prog rshape h
    rw [show ({ s with structs := [] } : PanSemStateFiniteExact 64 F).code = s.code from rfl,
      emptyCode] at h
    cases h
  obtain ⟨c', hev, hc'⟩ := PanSimp.evaluateDeclsCodeRel decls { s with structs := [] } _ s.code s1 rel hs1
  refine ⟨{ s1 with code := c' }, hev, ?_⟩
  obtain ⟨ev', run', le⟩ := simp_code_run run ok c' hc'
  exact ⟨_, ev', run', le.sharpScore⟩

#print axioms simp_top_entry
end InitECandidate.Runtime.FineCost
