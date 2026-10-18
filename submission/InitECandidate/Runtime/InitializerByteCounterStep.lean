import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.MemzeroSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def initializerByteCounterStep (destination value : ExpHOL 64) : ProgHOL 64 :=
  .seq (.storeByte destination value) (memzeroAdvance 1)

/-- Both initializer loops either reject at their byte store or advance the
word counter by one, with no body clock tick. -/
theorem evaluate_initializer_byte_counter_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (index : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state (initializerByteCounterStep destination value) = (result,post) ∧
      post.clock = state.clock ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 1)))) ∨ result = some .error) := by
  have facts := evaluate_storeByte_control_frame state destination value
  cases stored : evaluateHOLFiniteState state (.storeByte destination value) with
  | mk result middle =>
    rw [stored] at facts
    dsimp only at facts
    obtain ⟨control,clock,locals,_⟩ := facts
    rcases control with rfl | rfl
    · have atIndex : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by rw [locals]; exact indexLocal
      have advanced := evaluate_memzero_advance middle index 1 atIndex
      refine ⟨none,_,evaluate_seq_none stored advanced,clock,Or.inl ⟨rfl,?_⟩⟩
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · refine ⟨some .error,middle,?_,clock,Or.inr rfl⟩
      rw [initializerByteCounterStep,evaluateHOLFiniteState_seq_line780,stored]

#print axioms evaluate_initializer_byte_counter_step
end InitECandidate.Runtime
