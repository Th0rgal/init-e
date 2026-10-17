import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds two word arguments with any declared return shape. -/
theorem pan_two_word_lookup_shape {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (body : ProgHOL width) (returnShape : ShapeHOL) (left right : BitVec width)
    (different : first ≠ second)
    (lookup : code name = some ([(first,.one),(second,.one)],body,returnShape)) :
    lookupCodeHOLFinite code name [.val (.word left),.val (.word right)] =
      some (body,(HolFiniteMapExact.empty.update (first,.val (.word left))).update (second,.val (.word right)),returnShape) := by
  have raw : lookupCodeHOLExact code name [.val (.word left),.val (.word right)] =
      some (body,(fun key => if key = second then some (.val (.word right)) else if key = first then some (.val (.word left)) else none),returnShape) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL,different]
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
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,different,Ne.symm different]
    · have backOne : first ≠ key := Ne.symm one
      by_cases two : key = second
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
      · have backTwo : second ≠ key := Ne.symm two
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,one,two,backOne,backTwo]

#print axioms pan_two_word_lookup_shape
end InitECandidate.Runtime
