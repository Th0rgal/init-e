import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds three scalar arguments to distinct parameters, retaining the return shape. -/
theorem pan_three_value_lookup_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third : MlS) (body : ProgHOL width) (resultShape : ShapeHOL) (left right last : HolWordLab width)
    (different : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (lookup : code name = some ([(first,.one),(second,.one),(third,.one)],body,resultShape)) :
    lookupCodeHOLFinite code name [.val left,.val right,.val last] =
      some (body,((HolFiniteMapExact.empty.update (first,.val left)).update (second,.val right)).update (third,.val last),resultShape) := by
  have raw : lookupCodeHOLExact code name [.val left,.val right,.val last] =
      some (body,(fun key => if key = third then some (.val last) else if key = second then some (.val right) else if key = first then some (.val left) else none),resultShape) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL,different,firstThird,secondThird]
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

#print axioms pan_three_value_lookup_shape
end InitECandidate.Runtime
