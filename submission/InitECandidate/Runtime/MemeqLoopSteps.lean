import InitECandidate.Runtime.MemeqBody32
import InitECandidate.Runtime.ReadCheckAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memeqByte8Loop : ProgHOL 64 :=
  match memeqAfterAligned with
  | .seq loop _ => loop
  | _ => .skip

def memeqByte1Loop : ProgHOL 64 :=
  match memeqAfterAligned with
  | .seq _ (.seq loop _) => loop
  | _ => .skip

def memeqByte8Step : ProgHOL 64 :=
  match memeqByte8Loop with | .while _ body => body | _ => .skip

def memeqByte1Step : ProgHOL 64 :=
  match memeqByte1Loop with | .while _ body => body | _ => .skip

theorem source_memeq_byte_suffix : memeqAfterAligned =
    .seq memeqByte8Loop (.seq memeqByte1Loop (.return (.const 1))) := by rfl

theorem source_memeq_byte1_loop : memeqByte1Loop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memeqByte1Step := by rfl

theorem source_memeq_byte8_loop : memeqByte8Loop =
    .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 8])) memeqByte8Step := by rfl

theorem memeq_byte8_step_advances : ReadCheckAdvanceStep (ofString "i") 8 memeqByte8Step := by
  repeat first | exact ReadCheckAdvanceStep.advance | apply ReadCheckAdvanceStep.check

theorem memeq_byte1_step_advances : ReadCheckAdvanceStep (ofString "i") 1 memeqByte1Step := by
  repeat first | exact ReadCheckAdvanceStep.advance | apply ReadCheckAdvanceStep.check

/-- Exact control and counter contract for the original byte-at-a-time step. -/
theorem evaluate_memeq_byte1_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state memeqByte1Step = (result,post) ∧ post.clock = state.clock ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
        (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name)) ∨
       result = some .error ∨ result = some (.returned (.val (.word (0 : BitVec 64))))) :=
  evaluate_readCheckAdvanceStep memeq_byte1_step_advances state index binding

#print axioms source_memeq_byte_suffix
#print axioms source_memeq_byte1_loop
#print axioms source_memeq_byte8_loop
#print axioms memeq_byte8_step_advances
#print axioms memeq_byte1_step_advances
#print axioms evaluate_memeq_byte1_step
end InitECandidate.Runtime
