import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual finite lookup_code binds a word and a four-word struct argument. -/
theorem pan_word_struct4_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (body : ProgHOL width) (returnShape : ShapeHOL) (left : BitVec width) (m0 m1 m2 m3 : BitVec width)
    (different : first ≠ second)
    (lookup : code name = some ([(first,.one),(second,.comb [.one,.one,.one,.one])],body,returnShape)) :
    lookupCodeHOLFinite code name [.val (.word left),(.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)])] =
      some (body,(HolFiniteMapExact.empty.update (first,.val (.word left))).update (second,(.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)])),returnShape) := by
  have raw : lookupCodeHOLExact code name [.val (.word left),(.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)])] =
      some (body,(fun key => if key = second then some (.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)]) else if key = first then some (.val (.word left)) else none),returnShape) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,different]
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

#print axioms pan_word_struct4_lookup
end InitECandidate.Runtime
