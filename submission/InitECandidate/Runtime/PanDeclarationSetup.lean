import InitECandidate.Runtime.PanCrepEntryClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Exact guards for function/exception declaration initialization. The check
tracks exception names and validates the original parameter/return shapes. -/
def panDeclarationSetup {width : Nat} [NeZero width] (structs : StructContextExact)
    (exceptions : HolFiniteMapExact MlS ShapeHOL) : List (DeclHOL width) → Bool
  | [] => true
  | .name _ _ :: rest => panDeclarationSetup structs exceptions rest
  | .function decl :: rest =>
      (decl.params.all (fun parameter => isWfShapeExactHOL structs parameter.2) &&
        isWfShapeExactHOL structs decl.returnShape) && panDeclarationSetup structs exceptions rest
  | .exnDecl name shape :: rest =>
      ((exceptions.lookup name).isNone && isWfShapeExactHOL structs shape) &&
        panDeclarationSetup structs (exceptions.update (name,shape)) rest
  | .decl _ _ _ :: _ => false

/-- Successful declaration guards produce an actual original evaluator run;
no declaration evaluation or initialized target state is assumed. -/
theorem panDeclarationSetup_succeeds {width : Nat} [NeZero width] {F : Type}
    (code : List (DeclHOL width)) (s : PanSemStateFiniteExact width F) [DecidablePred s.memaddrs]
    (checked : panDeclarationSetup s.structs s.eshapes code = true) :
    ∃ post, evaluateDeclsHOLFinite s code = some post := by
  induction code generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons decl rest ih =>
    cases decl with
    | name name fields => exact ih s checked
    | decl shape name expression => simp [panDeclarationSetup] at checked
    | function decl =>
      simp only [panDeclarationSetup,Bool.and_eq_true] at checked
      obtain ⟨post,run⟩ := ih {s with code := s.code.update (decl.name,(decl.params,decl.body,decl.returnShape))} checked.2
      refine ⟨post,?_⟩
      rw [evaluateDeclsHOLFinite]
      rw [show (decl.params.all (fun parameter => isWfShapeExactHOL s.structs parameter.2) &&
        isWfShapeExactHOL s.structs decl.returnShape) = true from by simp [checked.1.1,checked.1.2]]
      exact run
    | exnDecl name shape =>
      simp only [panDeclarationSetup,Bool.and_eq_true] at checked
      obtain ⟨post,run⟩ := ih {s with eshapes := s.eshapes.update (name,shape)} checked.2
      refine ⟨post,?_⟩
      rw [evaluateDeclsHOLFinite]
      rw [show ((s.eshapes.lookup name).isNone && isWfShapeExactHOL s.structs shape) = true from by simp [checked.1.1,checked.1.2]]
      exact run

/-- Initialization changes precisely the function and exception tables. All
runtime fields, including the source clock, memory and FFI, are unchanged. -/
theorem panDeclarationSetup_evaluates {width : Nat} [NeZero width] {F : Type}
    (code : List (DeclHOL width)) (s : PanSemStateFiniteExact width F) [DecidablePred s.memaddrs]
    (checked : panDeclarationSetup s.structs s.eshapes code = true) :
    evaluateDeclsHOLFinite s code = some {s with
      code := s.code.updateList (functionsHOL code)
      eshapes := s.eshapes.updateList (exceptionsHOL code)} := by
  induction code generalizing s with
  | nil => rfl
  | cons decl rest ih =>
    cases decl with
    | name name fields => exact ih s checked
    | decl shape name expression => simp [panDeclarationSetup] at checked
    | function decl =>
      simp only [panDeclarationSetup,Bool.and_eq_true] at checked
      rw [evaluateDeclsHOLFinite]
      rw [show (decl.params.all (fun parameter => isWfShapeExactHOL s.structs parameter.2) &&
        isWfShapeExactHOL s.structs decl.returnShape) = true from by simp [checked.1.1,checked.1.2]]
      simp only [ite_true]
      rw [ih {s with code := s.code.update (decl.name,(decl.params,decl.body,decl.returnShape))} checked.2]
      rfl
    | exnDecl name shape =>
      simp only [panDeclarationSetup,Bool.and_eq_true] at checked
      rw [evaluateDeclsHOLFinite]
      rw [show ((s.eshapes.lookup name).isNone && isWfShapeExactHOL s.structs shape) = true from by simp [checked.1.1,checked.1.2]]
      simp only [ite_true]
      rw [ih {s with eshapes := s.eshapes.update (name,shape)} checked.2]
      rfl

#print axioms panDeclarationSetup_evaluates
#print axioms panDeclarationSetup_succeeds
end InitECandidate.Runtime
