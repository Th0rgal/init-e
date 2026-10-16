import Flapjack.Pancake.Proofs.PanSimp.StateRel
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

/-- The simplifier relation changes exactly code, in either direction. -/
theorem pan_simp_source_frame {width : Nat} [NeZero width] {F : Type}
    (source target : PanSemStateFiniteExact width F)
    (related : PanSimp.stateRel source target target.code) :
    source = {target with code := source.code} := by
  rw [related.1]
end InitECandidate.Runtime
