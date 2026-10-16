import InitECandidate.Runtime.PanDeclarationSetup
import InitECandidate.Runtime.SourceEntryCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

/-- Function-only declaration guards do not inspect exception tables. -/
theorem pan_function_setup_exceptions {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) (structs : StructContextExact)
    (first second : HolFiniteMapExact MlS ShapeHOL)
    (functions : declarations.all isFunctionHOL = true) :
    panDeclarationSetup structs first declarations = panDeclarationSetup structs second declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
    simp only [List.all_cons,Bool.and_eq_true] at functions
    cases declaration with
    | function fn =>
      simp only [panDeclarationSetup]
      rw [ih functions.2]
    | decl shape name expression => simp [isFunctionHOL] at functions
    | exnDecl name shape => simp [isFunctionHOL] at functions
    | name name fields => simp [isFunctionHOL] at functions

theorem source_entry_code_same_locals {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    sourceEntryCode state state.locals code = {state with code := code} := rfl

#print axioms pan_function_setup_exceptions
#print axioms source_entry_code_same_locals
end InitECandidate.Runtime
