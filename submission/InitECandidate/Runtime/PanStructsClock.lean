import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExact
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Structure lowering uses identical initial and remaining clocks while
preserving every original shape, value and execution conclusion. -/
theorem pan_structs_same_clock {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ) :
  ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width)),
    ( PanSemStateFiniteExact.evaluateHOLFiniteState source program = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) →
    (convertStateExact context source).clock = source.clock ∧
    (convertStateExact context post).clock = post.clock ∧
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context program) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  intro post context res h
  exact ⟨rfl,rfl,Pancake.Proofs.PanStructs.CompileCorrectExact.compileCorrectExact program source post context res h⟩

#print axioms pan_structs_same_clock
end InitECandidate.Runtime
