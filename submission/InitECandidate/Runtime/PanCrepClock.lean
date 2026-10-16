import InitECandidate.Runtime.CrepOptimizedCeiling
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

/-- Full original Pancake-to-Crep simulation uses identical initial fuel and
preserves the remaining clock; all original result and relation clauses remain. -/
theorem pan_crep_same_clock {width : Nat} {σ : Type} [NeZero width] :
    ∀ (v : ProgHOL width) (v1 : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
      (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (ctxt : PanToCrepContextExact width),
      v1.evaluateHOLFiniteState v = (res, s1) ∧
        res ≠ some .error ∧ panToCrepStateRelFiniteExact v1 t ∧
        codeRelExactHOLW ctxt v1.code t.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids v1.eshapes ∧
        panToCrepLocalsRelFiniteExact ctxt v1.locals t.locals ∧
        localisedProgHOL v = true →
      ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
        t.clock = v1.clock ∧ t1.clock = s1.clock ∧
        evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt v) =
          (res1, t1) ∧
        panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        match res with
        | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .error => False
        | some .timeOut => res1 = some .timeOut
        | some .break =>
            res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some .continue =>
            res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
        | some (.returned rv) => res1 = some (.return (flattenHOL rv))
        | some (.exception eid v') =>
            (match ctxt.eids.lookup eid with
             | none => False
             | some n =>
                 res1 = some (.exception n) ∧
                 (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                   globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                     sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
        | some (.finalFfi f) => res1 = some (.finalFfi f) := by
  intro v v1 res s1 t ctxt h
  obtain ⟨res1,t1,run,state,code,exceptions,outcome⟩ := pcCompileCorrect v v1 res s1 t ctxt h
  have initialState := h.2.2.1
  exact ⟨res1,t1,initialState.2.2.2.2.2.1.symm,state.2.2.2.2.2.1.symm,
    run,state,code,exceptions,outcome⟩

#print axioms pan_crep_same_clock
end InitECandidate.Runtime
