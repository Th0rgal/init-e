import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds one argument of any declared shape to its
parameter, provided that value really has that shape. -/
theorem pan_single_shape_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name parameter : MlS) (body : ProgHOL width) (parameterShape returnShape : ShapeHOL)
    (value : ValueHOL width)
    (lookup : code name = some ([(parameter, parameterShape)], body, returnShape))
    (shapeMatch : shapeEqHOL parameterShape (shapeOfHOLExact value) = true) :
    lookupCodeHOLFinite code name [value] =
      some (body, HolFiniteMapExact.empty.update (parameter, value), returnShape) := by
  have raw : lookupCodeHOLExact code name [value] =
      some (body,(fun key => if key = parameter then some value else none),returnShape) := by
    simp [lookupCodeHOLExact, lookup, shapeMatch]
  unfold lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl,rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody,locals,foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : key = parameter
    · subst same
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
    · have different : parameter ≠ key := Ne.symm same
      simp [same,different,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]

#print axioms pan_single_shape_lookup

/-- The actual finite lookup_code binds two arguments of declared shapes to their
parameters, provided both values have those shapes. -/
theorem pan_two_shape_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (body : ProgHOL width)
    (firstShape secondShape returnShape : ShapeHOL) (firstValue secondValue : ValueHOL width)
    (different : first ≠ second)
    (lookup : code name =
      some ([(first, firstShape), (second, secondShape)], body, returnShape))
    (firstMatch : shapeEqHOL firstShape (shapeOfHOLExact firstValue) = true)
    (secondMatch : shapeEqHOL secondShape (shapeOfHOLExact secondValue) = true) :
    lookupCodeHOLFinite code name [firstValue, secondValue] =
      some (body, (HolFiniteMapExact.empty.update (first, firstValue)).update
        (second, secondValue), returnShape) := by
  have raw : lookupCodeHOLExact code name [firstValue, secondValue] =
      some (body,(fun key => if key = second then some secondValue
        else if key = first then some firstValue else none),returnShape) := by
    simp [lookupCodeHOLExact, lookup, firstMatch, secondMatch, different]
  unfold lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl,rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody,locals,foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases one : key = first
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,
        different, Ne.symm different]
    · have backOne : first ≠ key := Ne.symm one
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
      · have backTwo : second ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,
          one,two,backOne,backTwo]

#print axioms pan_two_shape_lookup
end InitECandidate.Runtime
