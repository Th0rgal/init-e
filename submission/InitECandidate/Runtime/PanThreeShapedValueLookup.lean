import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds three arbitrary precisely shaped arguments to distinct parameters. -/
theorem pan_three_shaped_value_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third : MlS) (body : ProgHOL width) (left right last : ValueHOL width)
    (different : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (lookup : code name = some ([(first,shapeOfHOLExact left),(second,shapeOfHOLExact right),(third,shapeOfHOLExact last)],body,.one)) :
    lookupCodeHOLFinite code name [left,right,last] =
      some (body,((HolFiniteMapExact.empty.update (first,left)).update (second,right)).update (third,last),.one) := by
  have reflexive (shape : ShapeHOL) : shapeEqHOL shape shape=true := (shapeEqHOL_eq_true _ _).mpr rfl
  have raw : lookupCodeHOLExact code name [left,right,last] =
      some (body,(fun key => if key = third then some (last) else if key = second then some (right) else if key = first then some (left) else none),.one) := by
    simp [lookupCodeHOLExact,lookup,different,firstThird,secondThird,reflexive]
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
    by_cases three : key = third
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
    · have backThree := Ne.symm three
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,secondThird,Ne.symm secondThird]
      · have backTwo := Ne.symm two
        by_cases one : key = first
        · subst key
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
            different,Ne.symm different,firstThird,Ne.symm firstThird]
        · have backOne := Ne.symm one
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
            one,two,three,backOne,backTwo,backThree]

#print axioms pan_three_shaped_value_lookup
end InitECandidate.Runtime
