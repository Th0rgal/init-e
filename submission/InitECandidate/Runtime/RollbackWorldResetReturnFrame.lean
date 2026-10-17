import InitECandidate.Runtime.RollbackWorldResetReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Reset and return change only journal_n among the globals and retain code
and byte order, exposing metadata needed by the next journal operation. -/
theorem rollback_reset_return_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    let post := (evaluateHOLFiniteState state (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0)))).2
    post.code = state.code ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) := by
  let assigned := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) state
  have reset : evaluateHOLFiniteState state (.assign .global (ofString "journal_n") (.const 0)) = (none,assigned) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,lookupKvarHOLExact,counter,assigned]
  have run : evaluateHOLFiniteState state (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite assigned) := by
    rw [evaluateHOLFiniteState_seq_line780,reset]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  dsimp only
  rw [run]
  refine ⟨rfl,rfl,?_⟩
  intro name different
  simp [assigned,emptyLocalsHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms rollback_reset_return_frame
end InitECandidate.Runtime
