import InitECandidate.Runtime.HtabHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem normalRel_global_call {R} (pre : GlobalsPreorder R) (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyRel : ReturnedRel R body)
    (stable : ∀ a b v, R a b → R a (b.update (name,v))) :
    NormalRel R (.call (some (some (.global,name),none)) function arguments) := by
  unfold NormalRel
  unfold ReturnedRel at bodyRel
  intro F state post r code run cont
  rw [evaluateHOLFiniteState_call] at run
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [args] at run; simp only at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [lookup] at run; simp only at run
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      rw [lookup] at run
      dsimp only at run
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split at run
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
        rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at run
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp only at run; obtain ⟨rfl,rfl⟩ := Prod.mk.inj run; rcases cont with h | h | h | ⟨v,h⟩ <;> cases h; done)
            | skip
          all_goals (simp only at run; split at run)
          all_goals first
            | (split at run
               · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
                 exact stable _ _ w (bodyRel (callEntryStateHOLFinite state callee) bodyPost w code bodyRun)
               · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
                 rcases cont with h | h | h | ⟨v,h⟩ <;> cases h)
            | (obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
               rcases cont with h | h | h | ⟨v,h⟩ <;> cases h)

#print axioms normalRel_global_call
end InitECandidate.Runtime
