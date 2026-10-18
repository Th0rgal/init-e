import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds four word arguments to distinct parameters. -/
theorem pan_four_word_shape_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third fourth : MlS) (body : ProgHOL width) (returnShape : ShapeHOL) (left right last final : BitVec width)
    (different : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (firstFourth : first ≠ fourth) (secondFourth : second ≠ fourth) (thirdFourth : third ≠ fourth)
    (lookup : code name = some ([(first,.one),(second,.one),(third,.one),(fourth,.one)],body,returnShape)) :
    lookupCodeHOLFinite code name [.val (.word left),.val (.word right),.val (.word last),.val (.word final)] =
      some (body,(((HolFiniteMapExact.empty.update (first,.val (.word left))).update (second,.val (.word right))).update (third,.val (.word last))).update (fourth,.val (.word final)),returnShape) := by
  have raw : lookupCodeHOLExact code name [.val (.word left),.val (.word right),.val (.word last),.val (.word final)] =
      some (body,(fun key => if key = fourth then some (.val (.word final)) else if key = third then some (.val (.word last)) else if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none),returnShape) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL,different,firstThird,secondThird,firstFourth,secondFourth,thirdFourth]
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
    by_cases four : key = fourth
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
    · have backFour := Ne.symm four
      by_cases three : key = third
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,thirdFourth,Ne.symm thirdFourth]
      · have backThree := Ne.symm three
        by_cases two : key = second
        · subst key
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
            secondThird,Ne.symm secondThird,secondFourth,Ne.symm secondFourth]
        · have backTwo := Ne.symm two
          by_cases one : key = first
          · subst key
            simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
              different,Ne.symm different,firstThird,Ne.symm firstThird,firstFourth,Ne.symm firstFourth]
          · have backOne := Ne.symm one
            simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
              one,two,three,four,backOne,backTwo,backThree,backFour]

#print axioms pan_four_word_shape_lookup
end InitECandidate.Runtime
