import InitECandidate.Runtime.CrepUniformCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The original live-variable optimization preserves the numerical ceiling
for terminal executions, including the original FFI and state guarantees. -/
theorem crep_optimized_ceiling {width : Nat} [NeZero width] {σ : Type}
    (limit : Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (small : sizeOf p ≤ limit) (bounded : CrepCodeSize limit s) :
    ∀       (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact s p = (res, s1) ∧ crepToLoopStateRelExact s t ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        crepToLoopCodeRelExact ctxt s.code t.code ∧
        crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧ res ≠ some .error ∧
        (∀ n, res ≠ some (.break n)) ∧ (∀ n, res ≠ some (.continue n)) ∧ res ≠ none →
      ∃ (ck : Nat), ck ≤ workCeiling limit s.clock (sizeOf p) ∧ ∃ (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (ocompileHOLExact ctxt l p)
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        (match res with
         | none => False
         | some .error => False
         | some .timeOut => res1 = some .timeOut
         | some (.break _) => False
         | some (.continue _) => False
         | some (.return v) => res1 = some (.result (v.map wlabWlocExact))
         | some (.exception eid) => res1 = some (.exception (.word eid))
         | some (.finalFfi f) => res1 = some (.finalFfi f)) := by
  intro res s1 t ctxt l ⟨he, hs, hm, hg, hc, hl, hne, hnb, hnc, hnn⟩
  obtain ⟨ck, ckSmall, res1, t1, h1, h1s, h1m, h1g, h1c, h1r, _⟩ :=
    crep_uniform_ceiling limit p s small bounded res s1 t ctxt l he hne hs hm hg hc hl
  subst h1r
  have hopt := optimise_correct _ _ _ _ ⟨h1,
    by rcases res with _ | r
       · exact absurd rfl hnn
       · cases r <;> simp_all [resultToLoop],
    by intro n; rcases res with _ | r
       · exact absurd rfl hnn
       · cases r <;> simp_all [resultToLoop],
    by intro n; rcases res with _ | r
       · exact absurd rfl hnn
       · cases r <;> simp_all [resultToLoop],
    by rcases res with _ | r
       · exact absurd rfl hnn
       · cases r <;> simp [resultToLoop]⟩
  refine ⟨ck, ckSmall, resultToLoop res, t1, hopt, h1s, h1m, h1g, h1c, ?_⟩
  rcases res with _ | r
  · exact absurd rfl hnn
  · cases r with
    | error => exact absurd rfl hne
    | «break» n => exact absurd rfl (hnb n)
    | «continue» n => exact absurd rfl (hnc n)
    | _ => rfl

#print axioms crep_optimized_ceiling
end InitECandidate.Runtime
