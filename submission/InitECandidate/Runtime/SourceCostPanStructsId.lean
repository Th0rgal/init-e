import Flapjack.Pancake.PanStructs.CompileDeclsExact
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.Pancake.PanStructs.CompileShapeExact

/-! `pan_structs` on a program without named structures is the identity: no
named shapes, no named-structure expressions and no `Name` declarations. Its
executed-work transfer is then the trivial one (the same run). -/

mutual
  def structFreeShape : ShapeHOL → Bool
    | .one => true
    | .comb shapes => structFreeShapes shapes
    | .named _ => false
  def structFreeShapes : List ShapeHOL → Bool
    | [] => true
    | shape :: shapes => structFreeShape shape && structFreeShapes shapes
end

mutual
  def structFreeExp : ExpHOL 64 → Bool
    | .rstruct es | .op _ es | .panop _ es => structFreeExps es
    | .rfield _ e | .load32 e | .loadByte e => structFreeExp e
    | .load shape e => structFreeShape shape && structFreeExp e
    | .cmp _ a b | .shift _ a b => structFreeExp a && structFreeExp b
    | .nstruct _ _ | .nfield _ _ => false
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
  def structFreeExps : List (ExpHOL 64) → Bool
    | [] => true
    | e :: es => structFreeExp e && structFreeExps es
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

def structFreeProg : ProgHOL 64 → Bool
  | .dec _ shape value body => structFreeShape shape && structFreeExp value && structFreeProg body
  | .assign _ _ value | .return value | .raise _ value | .shMemLoad _ _ _ value => structFreeExp value
  | .primitive _ _ args => structFreeExps args
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => structFreeExp a && structFreeExp b
  | .seq a b => structFreeProg a && structFreeProg b
  | .ite e a b => structFreeExp e && structFreeProg a && structFreeProg b
  | .while e body => structFreeExp e && structFreeProg body
  | .call (some (_, some (_, _, handler))) _ args => structFreeExps args && structFreeProg handler
  | .call _ _ args => structFreeExps args
  | .decCall _ shape _ args body => structFreeShape shape && structFreeExps args && structFreeProg body
  | .extCall _ a b c d => structFreeExp a && structFreeExp b && structFreeExp c && structFreeExp d
  | _ => true
termination_by p => sizeOf p

theorem compileShape_structFree {α : Type} (context : List (MlS × List (α × ShapeHOL))) :
    ∀ shape : ShapeHOL, structFreeShape shape = true → compileShapeExact context shape = shape := by
  refine ShapeHOL.rec
    (motive_1 := fun shape => structFreeShape shape = true → compileShapeExact context shape = shape)
    (motive_2 := fun shapes => structFreeShapes shapes = true →
      compileShapesExact context shapes = shapes)
    ?_ ?_ ?_ ?_ ?_
  · intro _; rw [compileShapeExact]
  · intro shapes ih free
    rw [compileShapeExact, ih (by simpa [structFreeShape] using free)]
  · intro name free; simp [structFreeShape] at free
  · intro _; rw [compileShapesExact]
  · intro head tail ihHead ihTail free
    simp only [structFreeShapes, Bool.and_eq_true] at free
    rw [compileShapesExact, ihHead free.1, ihTail free.2]

theorem compileExp_structFree (context : ContextExact) :
    ∀ e : ExpHOL 64, structFreeExp e = true → compileExpExact context e = e := by
  refine ExpHOL.rec
    (motive_1 := fun e => structFreeExp e = true → compileExpExact context e = e)
    (motive_2 := fun es => structFreeExps es = true → compileExpsExact context es = es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _; unfold compileExpExact; rfl
  · intro kind name _; unfold compileExpExact; rfl
  · intro fields ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro index value ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro name fields _ free; simp [structFreeExp] at free
  · intro name value _ free; simp [structFreeExp] at free
  · intro shape address ih free
    simp only [structFreeExp, Bool.and_eq_true] at free
    rw [compileExpExact, ih free.2, compileShape_structFree _ shape free.1]
  · intro address ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro address ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro operator args ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro operator args ih free
    rw [compileExpExact, ih (by simpa [structFreeExp] using free)]
  · intro operator left right ihLeft ihRight free
    simp only [structFreeExp, Bool.and_eq_true] at free
    rw [compileExpExact, ihLeft free.1, ihRight free.2]
  · intro operator left right ihLeft ihRight free
    simp only [structFreeExp, Bool.and_eq_true] at free
    rw [compileExpExact, ihLeft free.1, ihRight free.2]
  · intro _; unfold compileExpExact; rfl
  · intro _; unfold compileExpExact; rfl
  · intro _; unfold compileExpExact; rfl
  · intro _; rw [compileExpsExact]
  · intro head tail ihHead ihTail free
    simp only [structFreeExps, Bool.and_eq_true] at free
    rw [compileExpsExact, ihHead free.1, ihTail free.2]
  · trivial
  · intros; trivial
  · intros; trivial

theorem compileProg_structFree :
    ∀ (p : ProgHOL 64) (context : ContextExact), structFreeProg p = true →
      compileProgExact context p = p
  | .dec name shape value body, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileShape_structFree _ shape free.1.1,
      compileExp_structFree context value free.1.2, compileProg_structFree body _ free.2]
  | .assign kind name value, context, free => by
    rw [compileProgExact, compileExp_structFree context value (by simpa [structFreeProg] using free)]
  | .primitive name operator args, context, free => by
    have h := compileExp_structFree context (.rstruct args) (by simpa [structFreeProg, structFreeExp] using free)
    rw [compileExpExact] at h
    simp only [ExpHOL.rstruct.injEq] at h
    rw [compileProgExact, h]
  | .store a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context a free.1, compileExp_structFree context b free.2]
  | .store32 a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context a free.1, compileExp_structFree context b free.2]
  | .storeByte a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context a free.1, compileExp_structFree context b free.2]
  | .seq a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileProg_structFree a _ free.1, compileProg_structFree b _ free.2]
  | .ite e a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context e free.1.1, compileProg_structFree a _ free.1.2,
      compileProg_structFree b _ free.2]
  | .while e body, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context e free.1, compileProg_structFree body _ free.2]
  | .call none name args, context, free => by
    have h := compileExp_structFree context (.rstruct args) (by simpa [structFreeProg, structFreeExp] using free)
    rw [compileExpExact] at h
    simp only [ExpHOL.rstruct.injEq] at h
    rw [compileProgExact]; simp only [h]
  | .call (some (target, none)) name args, context, free => by
    have h := compileExp_structFree context (.rstruct args) (by simpa [structFreeProg, structFreeExp] using free)
    rw [compileExpExact] at h
    simp only [ExpHOL.rstruct.injEq] at h
    rw [compileProgExact]; simp only [h]
  | .call (some (target, some (exception, bound, handler))) name args, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    have h := compileExp_structFree context (.rstruct args) (by simpa [structFreeExp] using free.1)
    rw [compileExpExact] at h
    simp only [ExpHOL.rstruct.injEq] at h
    rw [compileProgExact]; simp only [h, compileProg_structFree handler _ free.2]
  | .decCall name shape function args body, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    have h := compileExp_structFree context (.rstruct args) (by simpa [structFreeExp] using free.1.2)
    rw [compileExpExact] at h
    simp only [ExpHOL.rstruct.injEq] at h
    rw [compileProgExact, compileShape_structFree _ shape free.1.1, h, compileProg_structFree body _ free.2]
  | .extCall name a b c d, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context a free.1.1.1, compileExp_structFree context b free.1.1.2,
      compileExp_structFree context c free.1.2, compileExp_structFree context d free.2]
  | .return value, context, free => by
    rw [compileProgExact, compileExp_structFree context value (by simpa [structFreeProg] using free)]
  | .raise exception value, context, free => by
    rw [compileProgExact, compileExp_structFree context value (by simpa [structFreeProg] using free)]
  | .shMemStore size a b, context, free => by
    simp only [structFreeProg, Bool.and_eq_true] at free
    rw [compileProgExact, compileExp_structFree context a free.1, compileExp_structFree context b free.2]
  | .shMemLoad size kind name address, context, free => by
    rw [compileProgExact, compileExp_structFree context address (by simpa [structFreeProg] using free)]
  | .skip, context, _ => by unfold compileProgExact; rfl
  | .break, context, _ => by unfold compileProgExact; rfl
  | .continue, context, _ => by unfold compileProgExact; rfl
  | .tick, context, _ => by unfold compileProgExact; rfl
  | .annot tag text, context, _ => by unfold compileProgExact; rfl
termination_by p => sizeOf p

#print axioms compileExp_structFree
#print axioms compileProg_structFree

def structFreeDecls : List (DeclHOL 64) → Bool
  | [] => true
  | .function d :: ds => structFreeShapes (d.params.map Prod.snd) && structFreeShape d.returnShape &&
      structFreeProg d.body && structFreeDecls ds
  | .decl shape _ value :: ds => structFreeShape shape && structFreeExp value && structFreeDecls ds
  | .exnDecl _ shape :: ds => structFreeShape shape && structFreeDecls ds
  | .name _ _ :: _ => false

theorem compileParams_structFree {α : Type} (context : List (MlS × List (α × ShapeHOL))) :
    ∀ params : List (MlS × ShapeHOL), structFreeShapes (params.map Prod.snd) = true →
      params.map (fun p => (p.1, compileShapeExact context p.2)) = params
  | [], _ => rfl
  | (name, shape) :: rest, free => by
    simp only [List.map_cons, structFreeShapes, Bool.and_eq_true] at free
    simp only [List.map_cons, compileShape_structFree context shape free.1,
      compileParams_structFree context rest free.2]

theorem compileDecls_structFree :
    ∀ (decls : List (DeclHOL 64)) (context : ContextExact), structFreeDecls decls = true →
      (compileDeclsExact context decls).1 = decls
  | [], _, _ => by rw [compileDeclsExact]
  | .function d :: ds, context, free => by
    simp only [structFreeDecls, Bool.and_eq_true] at free
    rw [compileDeclsExact]
    simp only [compileParams_structFree _ _ free.1.1.1, compileShape_structFree _ _ free.1.1.2,
      compileProg_structFree _ _ free.1.2, compileDecls_structFree ds _ free.2]
  | .decl shape name value :: ds, context, free => by
    simp only [structFreeDecls, Bool.and_eq_true] at free
    rw [compileDeclsExact]
    simp only [compileShape_structFree _ _ free.1.1, compileExp_structFree _ _ free.1.2,
      compileDecls_structFree ds _ free.2]
  | .exnDecl name shape :: ds, context, free => by
    simp only [structFreeDecls, Bool.and_eq_true] at free
    rw [compileDeclsExact]
    simp only [compileShape_structFree _ _ free.1, compileDecls_structFree ds _ free.2]
  | .name _ _ :: _, _, free => by simp [structFreeDecls] at free

/-- `pan_structs$compile_top` is the identity on struct-free declarations, so
its executed-work transfer is the identity on the same canonical run. -/
theorem compileTop_structFree (decls : List (DeclHOL 64)) (free : structFreeDecls decls = true) :
    compileTopExact decls = decls := by
  unfold compileTopExact
  exact compileDecls_structFree decls _ free

#print axioms compileTop_structFree

#print axioms compileShape_structFree
end InitECandidate.Runtime.FineCost
