import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds a single word argument to its parameter. -/
theorem pan_single_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name parameter : MlS) (body : ProgHOL width) (amount : BitVec width)
    (lookup : code name = some ([(parameter,.one)],body,.one)) :
    lookupCodeHOLFinite code name [.val (.word amount)] =
      some (body,HolFiniteMapExact.empty.update (parameter,.val (.word amount)),.one) := by
  have raw : lookupCodeHOLExact code name [.val (.word amount)] =
      some (body,(fun key => if key = parameter then some (.val (.word amount)) else none),.one) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL]
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
    funext key
    by_cases same : key = parameter
    · subst same
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
    · have different : parameter ≠ key := Ne.symm same
      simp [same,different,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]

#print axioms pan_single_word_lookup
end InitECandidate.Runtime
