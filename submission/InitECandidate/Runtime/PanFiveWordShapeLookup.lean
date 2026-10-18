import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxHeartbeats 1000000

/-- Exact finite argument binding for five distinct word parameters. -/
theorem pan_five_word_shape_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third fourth fifth : MlS) (body : ProgHOL width) (returnShape : ShapeHOL)
    (a b c d e : BitVec width)
    (n12 : first ≠ second) (n13 : first ≠ third) (n14 : first ≠ fourth) (n15 : first ≠ fifth)
    (n23 : second ≠ third) (n24 : second ≠ fourth) (n25 : second ≠ fifth)
    (n34 : third ≠ fourth) (n35 : third ≠ fifth) (n45 : fourth ≠ fifth)
    (lookup : code name = some ([(first,.one),(second,.one),(third,.one),(fourth,.one),(fifth,.one)],body,returnShape)) :
    lookupCodeHOLFinite code name [.val (.word a),.val (.word b),.val (.word c),.val (.word d),.val (.word e)] =
      some (body,((((HolFiniteMapExact.empty.update (first,.val (.word a))).update (second,.val (.word b))).update
        (third,.val (.word c))).update (fourth,.val (.word d))).update (fifth,.val (.word e)),returnShape) := by
  have raw : lookupCodeHOLExact code name [.val (.word a),.val (.word b),.val (.word c),.val (.word d),.val (.word e)] =
      some (body,(fun key => if key = fifth then some (.val (.word e)) else if key = fourth then some (.val (.word d))
        else if key = third then some (.val (.word c)) else if key = second then some (.val (.word b))
        else if key = first then some (.val (.word a)) else none),returnShape) := by
    simp [lookupCodeHOLExact,lookup,shapeOfHOLExact,shapeEqHOL,n12,n13,n14,n15,n23,n24,n25,n34,n35,n45]
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
    by_cases five : key = fifth
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE]
    · by_cases four : key = fourth
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,n45,Ne.symm n45]
      · by_cases three : key = third
        · subst key
          simp [HolFiniteMapExact.lookup_update,FUPDATE,n34,Ne.symm n34,n35,Ne.symm n35]
        · by_cases two : key = second
          · subst key
            simp [HolFiniteMapExact.lookup_update,FUPDATE,n23,Ne.symm n23,n24,Ne.symm n24,n25,Ne.symm n25]
          · by_cases one : key = first
            · subst key
              simp [HolFiniteMapExact.lookup_update,FUPDATE,n12,Ne.symm n12,n13,Ne.symm n13,
                n14,Ne.symm n14,n15,Ne.symm n15]
            · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
                one,Ne.symm one,two,Ne.symm two,three,Ne.symm three,four,Ne.symm four,five,Ne.symm five]

#print axioms pan_five_word_shape_lookup
end InitECandidate.Runtime
