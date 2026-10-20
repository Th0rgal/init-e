import Flapjack.Pancake.PanToCrep.CompileExact
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! `crep_inline` with no inlinable function is the identity, so on programs
without `inline` declarations `pan_to_crep$compile_prog` installs exactly the
`compile_to_crep` bodies that the statement-level transfer relates to. -/

theorem inline_core_empty {width : Nat} [NeZero width] [BEq CrepInlineMapHOLName]
    [LawfulBEq CrepInlineMapHOLName]
    (inlineable : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inlineable.lookup key ≠ none → key ∈ supportKeys)
    (empty : ∀ key, inlineable.lookup key = none) :
    ∀ p : CrepProgHOL width, CrepInlineCanonical.inlineProgHOLCoreExact inlineable supportKeys support_spec p = p
  | .call none name arguments => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact]
    split
    · rfl
    · rename_i h; simp [empty name] at h
  | .call (some (returnNames, none)) name arguments => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact]
    split
    · rfl
    · split
      · rfl
      · rename_i h; simp [empty name] at h
  | .call (some (returnNames, some (handler, body))) name arguments => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact, inline_core_empty _ _ _ empty body]
  | .dec name value body => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact, inline_core_empty _ _ _ empty body]
  | .seq first second => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact, inline_core_empty _ _ _ empty first,
      inline_core_empty _ _ _ empty second]
  | .ite condition first second => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact, inline_core_empty _ _ _ empty first,
      inline_core_empty _ _ _ empty second]
  | .while condition body => by
    rw [CrepInlineCanonical.inlineProgHOLCoreExact, inline_core_empty _ _ _ empty body]
  | .skip => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .assign _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .store _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .store32 _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .storeByte _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .storeGlob _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .break _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .continue _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .extCall _ _ _ _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .raise _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .return _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .tick => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .primitive _ _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
  | .shMem _ _ _ => by unfold CrepInlineCanonical.inlineProgHOLCoreExact; rfl
termination_by p => sizeOf p

#print axioms inline_core_empty

/-- With no inlinable names, `crep_inline` returns its input unchanged. -/
theorem compileInlTop_nil {width : Nat} [NeZero width]
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    CrepInlineCanonical.compileInlTopHOLExact [] prog = prog := by
  unfold CrepInlineCanonical.compileInlTopHOLExact
    CrepInlineCanonical.compileInlProgHOLExactWithSupport
  have filtered : prog.filter (fun triple => ([] : List CrepInlineMapHOLName).contains triple.1) = [] := by
    simp
  have none0 : ∀ key, (CrepInlineCanonical.alistToFmapHOLExact
      (prog.filter (fun triple => ([] : List CrepInlineMapHOLName).contains triple.1))).lookup key = none := by
    rw [filtered]; intro key; rfl
  conv => rhs; rw [← List.map_id prog]
  apply List.map_congr_left
  rintro ⟨name, params, body⟩ _
  have empty : ∀ key, ((CrepInlineCanonical.alistToFmapHOLExact
      (prog.filter (fun triple => ([] : List CrepInlineMapHOLName).contains triple.1))).erase
        name).lookup key = none := by
    intro key
    rw [HolFiniteMapExact.lookup_erase]
    simp only [FDOMSUB]
    split
    · rfl
    · exact none0 key
  exact congrArg (fun b => (name, params, b)) (inline_core_empty _ _ _ empty body)

/-- On programs without `inline` declarations, `pan_to_crep$compile_prog`
is exactly `compile_to_crep`. -/
theorem compileProgDecls_noInline {width : Nat} [NeZero width] (prog : List (DeclHOL width))
    (noInline : (functionsHOL (prog.filter inlinableHOL)).map Prod.fst = []) :
    compileProgDeclsHOLW prog = compileToCrepExactHOLW prog := by
  unfold compileProgDeclsHOLW
  simp only [noInline]
  exact compileInlTop_nil _

#print axioms compileInlTop_nil
#print axioms compileProgDecls_noInline
end InitECandidate.Runtime.FineCost
