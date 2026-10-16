import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Simplification only changes function bodies. Successful declaration
initialization therefore reflects to the original declarations, for any code map. -/
theorem pan_simp_declarations_reflect {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (state : PanSemStateFiniteExact width F)
    (h : DecidablePred state.memaddrs)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (targetPost : PanSemStateFiniteExact width F)
    (run : @evaluateDeclsHOLFinite width F _ {state with code := code} h
      (panSimpDeclsHOL declarations) = some targetPost) :
    ∃ sourcePost, @evaluateDeclsHOLFinite width F _ state h declarations = some sourcePost := by
  classical
  induction declarations generalizing state code with
  | nil => exact ⟨state,rfl⟩
  | cons declaration declarations ih =>
    cases declaration with
    | name name fields =>
      simp only [panSimpDeclsHOL,evaluateDeclsHOLFinite] at run ⊢
      exact ih state h code run
    | decl shape name expression =>
      simp only [panSimpDeclsHOL,evaluateDeclsHOLFinite] at run
      have expressionEq : @evalHOLFinite width F _ (emptyLocalsHOLFinite {state with code := code}) h expression =
          @evalHOLFinite width F _ (emptyLocalsHOLFinite state) h expression :=
        @evalHOLFinite_upd_code_eq width F _ (emptyLocalsHOLFinite state) h code expression
      rw [expressionEq] at run
      cases valueRun : @evalHOLFinite width F _ (emptyLocalsHOLFinite state) h expression with
      | none => simp only [valueRun] at run; cases run
      | some value =>
        simp only [valueRun] at run
        by_cases shapeOk : shapeEqHOL shape (shapeOfHOLExact value) = true
        · rw [if_pos shapeOk] at run
          obtain ⟨post,tailRun⟩ := ih (setGlobalHOLFinite name value state) h code run
          refine ⟨post,?_⟩
          simp only [evaluateDeclsHOLFinite,valueRun,if_pos shapeOk]
          exact tailRun
        · rw [if_neg shapeOk] at run; cases run
    | function fn =>
      simp only [panSimpDeclsHOL,evaluateDeclsHOLFinite] at run
      by_cases shapes : (fn.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
          isWfShapeExactHOL state.structs fn.returnShape) = true
      · rw [if_pos shapes] at run
        obtain ⟨post,tailRun⟩ := ih
          {state with code := state.code.update (fn.name,(fn.params,fn.body,fn.returnShape))}
          h (code.update (fn.name,(fn.params,panSimpCompileHOL fn.body,fn.returnShape))) run
        refine ⟨post,?_⟩
        simp only [evaluateDeclsHOLFinite,if_pos shapes]
        exact tailRun
      · rw [if_neg shapes] at run; cases run
    | exnDecl name shape =>
      simp only [panSimpDeclsHOL,evaluateDeclsHOLFinite] at run
      by_cases shapeOk : ((state.eshapes.lookup name).isNone && isWfShapeExactHOL state.structs shape) = true
      · rw [if_pos shapeOk] at run
        obtain ⟨post,tailRun⟩ := ih {state with eshapes := state.eshapes.update (name,shape)} h code run
        refine ⟨post,?_⟩
        simp only [evaluateDeclsHOLFinite,if_pos shapeOk]
        exact tailRun
      · rw [if_neg shapeOk] at run; cases run

#print axioms pan_simp_declarations_reflect
end InitECandidate.Runtime
