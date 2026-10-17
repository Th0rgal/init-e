import InitECandidate.Runtime.StoreAdvance8Step
import InitECandidate.Runtime.MemzeroSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString


/-- A failed store exits; a completed store reaches the exact eight-byte
counter advance. Both branches consume zero source clock. -/
theorem evaluate_store_advance8_step_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (index : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state (storeAdvance8Body destination value) = (result,post) ∧
      post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 8)))) ∨ result = some .error) := by
  have facts := evaluate_store_control_frame state destination value
  cases stored : evaluateHOLFiniteState state (.store destination value) with
  | mk result middle =>
    rw [stored] at facts
    obtain ⟨control,locals,clock⟩ := facts
    rcases control with rfl | rfl
    · have atIndex : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by rw [locals]; exact indexLocal
      have advanced := evaluate_memzero_advance middle index 8 atIndex
      refine ⟨none,_,evaluate_seq_none stored advanced,clock,?_,Or.inl ⟨rfl,?_⟩⟩
      · intro name different
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
        exact congrArg (fun map => map.lookup name) locals
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · refine ⟨some .error,middle,?_,clock,(by intro name _; rw [locals]),Or.inr rfl⟩
      unfold storeAdvance8Body
      rw [evaluateHOLFiniteState_seq_line780,stored]

#print axioms evaluate_store_advance8_step_frame
end InitECandidate.Runtime
