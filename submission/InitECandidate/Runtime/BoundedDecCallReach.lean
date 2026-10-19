import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A bounded actual declaration callee either reaches its continuation with
facts derived from its checked return, or terminates within the callee budget. -/
theorem bounded_decCall_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (cost : Nat)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape))
    (budget : cost + 1 ≤ s.clock)
    (bounded : RunBounded (callEntryStateHOLFinite s callee) body cost)
    (property : ∀ value post, evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned value),post) →
      (shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) returnShape = true) →
      P (setVarHOLFinite name value {post with locals := s.locals})) :
    Reaches s (.decCall name shape function arguments continuation) P (cost + 1) continuation := by
  have bound := bounded
  unfold RunBounded at bound
  rw [Reaches,evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg (by omega : s.clock ≠ 0)]
  rw [fixClockHOLFinite_evaluateState]
  cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
  | mk result post =>
    rw [bodyRun] at bound
    obtain ⟨spent,kept,safe⟩ := bound
    change s.clock - 1 ≤ post.clock + cost at spent
    change post.clock ≤ s.clock - 1 at kept
    cases result with
    | none =>
      right
      exact ⟨.error,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
        (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
    | some r =>
      cases r with
      | returned value =>
        dsimp only
        split
        · rename_i ok
          have checked : shapeEqHOL (shapeOfHOLExact value) shape = true ∧
              shapeEqHOL (shapeOfHOLExact value) returnShape = true := by simpa using ok
          left
          refine ⟨setVarHOLFinite name value {post with locals := s.locals},property value post bodyRun checked,
            (by change s.clock ≤ post.clock + (cost + 1); omega),(by change post.clock ≤ s.clock; omega),?_⟩
          exact scoped_restore (evaluateHOLFiniteState (setVarHOLFinite name value {post with locals := s.locals}) continuation) _
        · right
          exact ⟨.error,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
            (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
      | timeOut => exact False.elim (safe rfl)
      | error =>
        right
        exact ⟨.error,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
          (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
      | «break» =>
        right
        exact ⟨.error,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
          (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
      | «continue» =>
        right
        exact ⟨.error,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
          (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
      | exception tag value =>
        right
        exact ⟨.exception tag value,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
          (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩
      | finalFfi ffi =>
        right
        exact ⟨.finalFfi ffi,rfl,(by intro v h; cases h),(by change s.clock ≤ post.clock + (cost + 1); omega),
          (by change post.clock ≤ s.clock; omega),(by intro _ h; cases h)⟩

#print axioms bounded_decCall_reaches
end InitECandidate.Runtime
