import InitECandidate.Runtime.PanTotalExpressionCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def ReadsPresent {F : Type} (s : PanSemStateExact 64 F) (names : List MlStringHOL) : Prop :=
  ∀ name, name ∈ names → ∃ value, s.locals name = some value

/-- Successful exact evaluation entails presence of every syntactically read
local, including fields and arbitrary operand lists. No layout premise is used. -/
theorem eval_success_reads_present {F : Type} (s : PanSemStateExact 64 F)
    [DecidablePred s.memaddrs] :
    ∀ e : ExpHOL 64, ∀ value, evalHOLExact s e = some value → ReadsPresent s (varExpHOL e) := by
  refine ExpHOL.rec
    (motive_1 := fun e => ∀ value, evalHOLExact s e = some value → ReadsPresent s (varExpHOL e))
    (motive_2 := fun es => ∀ values, evalListHOLExact s es = some values →
      ReadsPresent s ((es.map varExpHOL).flatten))
    (motive_3 := fun fields => ∀ values, evalListFieldsHOLExact s fields = some values →
      ReadsPresent s ((fields.map (fun pair => varExpHOL pair.2)).flatten))
    (motive_4 := fun pair : MlStringHOL × ExpHOL 64 => ∀ value,
      evalHOLExact s pair.2 = some value → ReadsPresent s (varExpHOL pair.2))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro word value evaluated name member
    simp [varExpHOL] at member
  · intro kind varName value evaluated name member
    cases kind with
    | «local» =>
      simp only [varExpHOL, List.mem_singleton] at member
      subst name
      exact ⟨value, evaluated⟩
    | «global» => simp [varExpHOL] at member
  · intro fields ih value evaluated
    cases hc : evalListHOLExact s fields with
    | none => simp [evalHOLExact, hc] at evaluated
    | some values => simpa only [varExpHOL] using ih values hc
  · intro index child ih value evaluated
    cases hc : evalHOLExact s child with
    | none => simp [evalHOLExact, hc] at evaluated
    | some result => simpa only [varExpHOL] using ih result hc
  · intro structName fields ih value evaluated
    cases hc : evalListFieldsHOLExact s fields with
    | none =>
      simp only [evalHOLExact, hc] at evaluated
      repeat' split at evaluated
      all_goals simp_all
    | some values => simpa only [varExpHOL] using ih values hc
  · intro field child ih value evaluated
    cases hc : evalHOLExact s child with
    | none => simp [evalHOLExact, hc] at evaluated
    | some result => simpa only [varExpHOL] using ih result hc
  · intro shape child ih value evaluated
    cases hc : evalHOLExact s child with
    | none => simp [evalHOLExact, hc] at evaluated
    | some result => simpa only [varExpHOL] using ih result hc
  · intro child ih value evaluated
    cases hc : evalHOLExact s child with
    | none => simp [evalHOLExact, hc] at evaluated
    | some result => simpa only [varExpHOL] using ih result hc
  · intro child ih value evaluated
    cases hc : evalHOLExact s child with
    | none => simp [evalHOLExact, hc] at evaluated
    | some result => simpa only [varExpHOL] using ih result hc
  · intro operator args ih value evaluated
    cases hc : evalListHOLExact s args with
    | none => simp [evalHOLExact, hc] at evaluated
    | some values => simpa only [varExpHOL] using ih values hc
  · intro operator args ih value evaluated
    cases hc : evalListHOLExact s args with
    | none => simp [evalHOLExact, hc] at evaluated
    | some values => simpa only [varExpHOL] using ih values hc
  · intro operator left right ihLeft ihRight value evaluated name member
    simp only [varExpHOL, List.mem_append] at member
    rcases member with member | member
    · cases hc : evalHOLExact s left with
      | none => simp [evalHOLExact, hc] at evaluated
      | some v => exact ihLeft v hc name member
    · cases hc : evalHOLExact s right with
      | none => simp [evalHOLExact, hc] at evaluated
      | some v => exact ihRight v hc name member
  · intro operator left right ihLeft ihRight value evaluated name member
    simp only [varExpHOL, List.mem_append] at member
    rcases member with member | member
    · cases hc : evalHOLExact s left with
      | none => simp [evalHOLExact, hc] at evaluated
      | some v => exact ihLeft v hc name member
    · cases hc : evalHOLExact s right with
      | none => simp [evalHOLExact, hc] at evaluated
      | some v => exact ihRight v hc name member
  · intro value evaluated name member; simp [varExpHOL] at member
  · intro value evaluated name member; simp [varExpHOL] at member
  · intro value evaluated name member; simp [varExpHOL] at member
  · intro values evaluated name member; simp at member
  · intro head tail ihHead ihTail values evaluated name member
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at member
    cases hh : evalHOLExact s head with
    | none => simp [evalListHOLExact, hh] at evaluated
    | some first =>
      cases ht : evalListHOLExact s tail with
      | none => simp [evalListHOLExact, ht] at evaluated
      | some rest =>
        rcases member with member | member
        · exact ihHead first hh name member
        · exact ihTail rest ht name member
  · intro values evaluated name member; simp at member
  · intro head tail ihHead ihTail values evaluated name member
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at member
    obtain ⟨field, expression⟩ := head
    cases hh : evalHOLExact s expression with
    | none => simp [evalListFieldsHOLExact, hh] at evaluated
    | some first =>
      cases ht : evalListFieldsHOLExact s tail with
      | none => simp [evalListFieldsHOLExact, ht] at evaluated
      | some rest =>
        rcases member with member | member
        · exact ihHead first hh name member
        · exact ihTail rest ht name member
  · intro field expression ih
    exact ih

/-- Finite-map form used by the compiler cost transfer. -/
theorem expression_success_locals_present {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value) :
    ∀ name, name ∈ varExpHOL e → ∃ value, s.locals.lookup name = some value := by
  have present := @eval_success_reads_present F s.toExact
    (fun a => Classical.propDecidable (s.memaddrs a)) e value evaluated
  exact present

#print axioms eval_success_reads_present
#print axioms expression_success_locals_present
end InitECandidate.Runtime.FineCost
