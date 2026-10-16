import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code installs empty locals for a zero-argument callee. -/
theorem pan_no_args_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (body : ProgHOL width)
    (lookup : code name = some ([],body,.one)) :
    lookupCodeHOLFinite code name [] =
      some (body,HolFiniteMapExact.empty,.one) := by
  have raw : lookupCodeHOLExact code name [] = some (body,(fun _ => none),.one) := by
    simp [lookupCodeHOLExact,lookup]
  unfold lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl,rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody,locals,ShapeHOL.one))
    apply HolFiniteMapExact.ext
    rfl

#print axioms pan_no_args_lookup
end InitECandidate.Runtime
