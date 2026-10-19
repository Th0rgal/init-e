import InitE.SourceMainFacts
import InitE.SourceSemantics
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.Pancake.PanToTarget
open Flapjack.PanSemStateFiniteExact

/-- Main-first normalization preserves the actual struct context and the
entire initialized source state, at the original clock. -/
theorem mainFirst_context_and_evaluation {width : Nat} [NeZero width] {F : Type}
    (program : List (DeclHOL width))
    (hasMain : ∃ fi : FunDeclHOL width, .function fi ∈ program ∧
      fi.name = Flapjack.Basis.Pure.MlString.ofString "main") :
    decsStcnamesHOLExact [] (mainFirstHOL program) = decsStcnamesHOLExact [] program ∧
      ∀ (state : PanSemStateFiniteExact width F) [DecidablePred state.memaddrs],
        evaluateDeclsHOLFinite state (mainFirstHOL program) =
          evaluateDeclsHOLFinite state program := by
  obtain ⟨before, fi, rest, original, distinct, moved⟩ := mainFirstHOL_of_main program hasMain
  constructor
  · rw [moved, original]
    change decsStcnamesHOLExact [] (before ++ rest) =
      decsStcnamesHOLExact [] (before ++ .function fi :: rest)
    exact (decsStcnamesHOLExact_dropFunction fi rest before []).symm
  · intro state inst
    rw [moved, original]
    exact (evaluateDeclsHOLFinite_moveFunction fi rest before distinct state).symm

theorem original_declaration_context :
    decsStcnamesHOLExact [] sourceDeclarations =
      decsStcnamesHOLExact [] (Guest.guestAst.map declToHOL) :=
  (mainFirst_context_and_evaluation (F := Guest.HostMemory)
    (Guest.guestAst.map declToHOL) sourceHasMain).1

theorem original_declaration_evaluation (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    [DecidablePred state.memaddrs] :
    evaluateDeclsHOLFinite state sourceDeclarations =
      evaluateDeclsHOLFinite state (Guest.guestAst.map declToHOL) :=
  (mainFirst_context_and_evaluation (Guest.guestAst.map declToHOL) sourceHasMain).2 state
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.mainFirst_context_and_evaluation
#print axioms InitECandidate.Runtime.original_declaration_context
#print axioms InitECandidate.Runtime.original_declaration_evaluation
