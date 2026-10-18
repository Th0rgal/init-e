import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Successful argument binding cannot replace the installed function body. -/
theorem lookupCodeHOLFinite_installed_body
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (parameters : List (MlS × ShapeHOL)) (body foundBody : ProgHOL 64)
    (returnShape foundShape : ShapeHOL) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (installed : code name = some (parameters,body,returnShape))
    (found : lookupCodeHOLFinite code name values = some (foundBody,locals,foundShape)) :
    foundBody = body := by
  unfold lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i exactBody exactLocals exactShape raw
    have same : exactBody = body := by
      simp only [lookupCodeHOLExact,installed] at raw
      split at raw
      · exact ((Prod.mk.inj (Option.some.inj raw)).1).symm
      · cases raw
    have equal := Option.some.inj found
    exact ((Prod.mk.inj equal).1).symm.trans same

#print axioms lookupCodeHOLFinite_installed_body
end InitECandidate.Runtime
