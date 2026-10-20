import InitECandidate.Runtime.RlpPutBeMemoryWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A sequence whose first part completes normally is exactly the evaluation of the second part from
the state the first part produced. -/
theorem seq_normal {F : Type} (s : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    {out : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s first = (none, out)) :
    evaluateHOLFiniteState s (.seq first second) = evaluateHOLFiniteState out second := by
  rw [evaluateHOLFiniteState_seq_line780]
  simp only [h]

#print axioms seq_normal

/-- A sequence whose first part stops with an error stops there, with the same state. -/
theorem seq_stops {F : Type} (s : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    {out : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s first = (some .error, out)) :
    evaluateHOLFiniteState s (.seq first second) = (some .error, out) := by
  rw [evaluateHOLFiniteState_seq_line780]
  simp only [h]

#print axioms seq_stops

/-- A local assignment to `name` leaves every other local readable as before, whatever the outcome of
the initializer or of the shape check. -/
theorem lookup_assign_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (name other : MlS)
    (expression : ExpHOL 64) (x : ValueHOL 64) (ne : name ≠ other)
    (h : s.locals.lookup other = some x) :
    (evaluateHOLFiniteState s (.assign .local name expression)).2.locals.lookup other = some x := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact h
  · split
    · rw [setKvarHOLFinite]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne,h]
    · exact h

#print axioms lookup_assign_ne

/-- The first local assignment of one `rlp_put_be` iteration, with its exact post state. -/
theorem rlpPutBeIndexAssign {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I))) :
    evaluateHOLFiniteState s (.assign .local (ofString "i")
      (.op .sub [.var .local (ofString "i"), .const (1#64)])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (I - 1#64))) s) := by
  rw [evaluateHOLFiniteState_assign]
  simp [evalListHOLExact,evalHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord,
    isValidValueHOLExact,lookupKvarHOLExact,shapeEqHOL,shapeOfHOLExact,setKvarHOLFinite]

#print axioms rlpPutBeIndexAssign

/-- One `rlp_put_be` iteration always leaves `dst = D` and turns `i = I` into `i = I - 1`,
whatever the outcome of the byte store or of the value shift: the index assignment is the only local
write besides the value shift, the byte store touches no local at all, and the index assignment itself
cannot fail. -/
theorem rlpPutBeStep_locals {F : Type} (s : PanSemStateFiniteExact 64 F) (D I : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I))) :
    (evaluateHOLFiniteState s rlpPutBeStep).2.locals.lookup (ofString "i") =
        some (.val (.word (I - 1#64))) ∧
      (evaluateHOLFiniteState s rlpPutBeStep).2.locals.lookup (ofString "dst") =
        some (.val (.word D)) := by
  let sA : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "i") (.val (.word (I - 1#64))) s
  let dest : ExpHOL 64 := .op .add [.var .local (ofString "dst"), .var .local (ofString "i")]
  let val : ExpHOL 64 := .var .local (ofString "v")
  let bytes : ProgHOL 64 := .storeByte dest val
  let shift : ProgHOL 64 := .assign .local (ofString "v")
    (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))
  have index : evaluateHOLFiniteState s (.assign .local (ofString "i")
      (.op .sub [.var .local (ofString "i"), .const (1#64)])) = (none, sA) :=
    rlpPutBeIndexAssign s I hi
  have hdA : sA.locals.lookup (ofString "dst") = some (.val (.word D)) :=
    lookup_setVar_ne s (ofString "i") (ofString "dst") _ _ (by decide) hd
  have hiA : sA.locals.lookup (ofString "i") = some (.val (.word (I - 1#64))) :=
    lookup_setVar_eq s (ofString "i") _
  have hmain : evaluateHOLFiniteState s rlpPutBeStep = evaluateHOLFiniteState sA (.seq bytes shift) := by
    simp only [rlpPutBeStep, bytes, shift, dest, val]
    rw [seq_normal (s := s) (first := .assign .local (ofString "i")
      (.op .sub [.var .local (ofString "i"), .const (1#64)]))
      (second := .seq bytes shift) index]
  rw [hmain]
  let sB : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState sA bytes).2
  have control := evaluate_storeByte_control_frame sA dest val
  have localsB : sB.locals = sA.locals := control.2.2.1
  have hiB : sB.locals.lookup (ofString "i") = some (.val (.word (I - 1#64))) := by
    rw [localsB]; exact hiA
  have hdB : sB.locals.lookup (ofString "dst") = some (.val (.word D)) := by
    rw [localsB]; exact hdA
  by_cases hB : (evaluateHOLFiniteState sA bytes).1 = none
  · have hBpair : evaluateHOLFiniteState sA bytes = (none, sB) := Prod.ext hB rfl
    rw [seq_normal (s := sA) (first := bytes) (second := shift) hBpair]
    exact ⟨lookup_assign_ne sB (ofString "v") (ofString "i")
        (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))
        (.val (.word (I - 1#64))) (by decide) hiB,
      lookup_assign_ne sB (ofString "v") (ofString "dst")
        (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))
        (.val (.word D)) (by decide) hdB⟩
  · have hErr : (evaluateHOLFiniteState sA bytes).1 = some .error := by
      rcases control.1 with h | h
      · exact absurd h hB
      · exact h
    have hErrpair : evaluateHOLFiniteState sA bytes = (some .error, sB) := Prod.ext hErr rfl
    rw [seq_stops (s := sA) (first := bytes) (second := shift) hErrpair]
    dsimp only
    exact ⟨hiB,hdB⟩

#print axioms rlpPutBeStep_locals

end InitECandidate.Runtime
