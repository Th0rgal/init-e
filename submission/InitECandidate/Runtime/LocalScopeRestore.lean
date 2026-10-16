import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Restore the previous binding after a temporary scoped local update,
including the case where the local was absent before entering the scope. -/
theorem restore_updated_local {A B : Type} [BEq A] [LawfulBEq A] [DecidableEq A]
    (locals : HolFiniteMapExact A B) (name : A) (value : B) :
    HolFiniteMapExact.resVarEq (locals.update (name,value)) (name,locals.lookup name) = locals := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases same : key = name
  · subst key
    cases saved : locals.lookup name <;>
      simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_eraseEq,FUPDATE_HOL,FDOMSUB_HOL]
  · have different : name ≠ key := Ne.symm same
    cases saved : locals.lookup name <;>
      simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_update,
        HolFiniteMapExact.lookup_updateEq,HolFiniteMapExact.lookup_eraseEq,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,same,different]

/-- A scoped local can be removed without disturbing the other source fields. -/
theorem restore_setVar_state {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F) (name : MlS) (value : ValueHOL width) :
    {setVarHOLFinite name value state with locals := (HolFiniteMapExact.resVarEq (setVarHOLFinite name value state).locals (name,state.locals.lookup name))} = state := by
  change {state with locals := (HolFiniteMapExact.resVarEq (state.locals.update (name,value)) (name,state.locals.lookup name))} = state
  rw [restore_updated_local]

/-- The same restoration applies when the body changed memory or other
runtime fields, provided it preserved its entered local environment. -/
theorem restore_body_locals {width : Nat} [NeZero width] {F : Type}
    (state post : PanSemStateFiniteExact width F) (name : MlS) (value : ValueHOL width)
    (preserved : post.locals = (setVarHOLFinite name value state).locals) :
    HolFiniteMapExact.resVarEq post.locals (name,state.locals.lookup name) = state.locals := by
  rw [preserved]
  exact restore_updated_local state.locals name value

/-- Leaving one scope cannot undo changes to another local, such as the
run_frames go flag set by a terminal frame branch. -/
theorem restore_other_local {A B : Type} [DecidableEq A]
    (locals : HolFiniteMapExact A B) (name key : A) (saved : Option B) (different : key ≠ name) :
    (HolFiniteMapExact.resVarEq locals (name,saved)).lookup key = locals.lookup key := by
  have backwards : name ≠ key := Ne.symm different
  cases saved <;> simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
    HolFiniteMapExact.lookup_eraseEq,FUPDATE_HOL,FDOMSUB_HOL,different,backwards]

/-- Actual declaration evaluation restores its caller local map while keeping
all effects of the body on memory and the other runtime fields. -/
theorem evaluate_scoped_body_preserving_locals {width : Nat} [NeZero width] {F : Type}
    (state post : PanSemStateFiniteExact width F) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) (value : ValueHOL width)
    (result : Option (PanSemResultExact width))
    (initial : @evalHOLExact width F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some value)
    (shapeOk : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (run : evaluateHOLFiniteState (setVarHOLFinite name value state) body = (result,post))
    (preserved : post.locals = (setVarHOLFinite name value state).locals) :
    evaluateHOLFiniteState state (.dec name shape initializer body) = (result,{post with locals := state.locals}) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [if_pos shapeOk,run]
  rw [restore_body_locals state post name value preserved]

#print axioms evaluate_scoped_body_preserving_locals

#print axioms restore_other_local
#print axioms restore_updated_local
#print axioms restore_setVar_state
#print axioms restore_body_locals
end InitECandidate.Runtime
