import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds three word arguments to distinct parameters. -/
theorem pan_three_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third : MlS) (body : ProgHOL width) (left right last : BitVec width)
    (different : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (lookup : code name = some ([(first,.one),(second,.one),(third,.one)],body,.one)) :
    lookupCodeHOLFinite code name [.val (.word left),.val (.word right),.val (.word last)] =
      some (body,((HolFiniteMapExact.empty.update (first,.val (.word left))).update (second,.val (.word right))).update (third,.val (.word last)),.one) := by
  have raw : lookupCodeHOLExact code name [.val (.word left),.val (.word right),.val (.word last)] =
      some (body,(fun key => if key = third then some (.val (.word last)) else if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none),.one) := by
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
    apply congrArg (fun locals => some (foundBody,locals,ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases three : key = third
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
    · have backThree := Ne.symm three
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,secondThird,Ne.symm secondThird]
      · have backTwo := Ne.symm two
        by_cases one : key = first
        · subst key
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,
            different,Ne.symm different,firstThird,Ne.symm firstThird]
        · have backOne := Ne.symm one
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,
            one,two,three,backOne,backTwo,backThree]

#print axioms pan_three_word_lookup
end InitECandidate.Runtime
