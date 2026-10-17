import InitECandidate.Runtime.MemeqLoopSteps
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memeqWord32Loop : ProgHOL 64 :=
  match memeqAlignedBody with
  | .seq _ (.seq _ (.seq _ (.seq loop _))) => loop
  | _ => .skip

def memeqWord8Loop : ProgHOL 64 :=
  match memeqAlignedBody with
  | .seq _ (.seq _ (.seq _ (.seq _ loop))) => loop
  | _ => .skip

def memeqWord32Step : ProgHOL 64 :=
  match memeqWord32Loop with | .while _ body => body | _ => .skip

def memeqWord8Step : ProgHOL 64 :=
  match memeqWord8Loop with | .while _ body => body | _ => .skip

theorem source_memeq_word32_loop : memeqWord32Loop =
    .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 32])) memeqWord32Step := by rfl

theorem source_memeq_word8_loop : memeqWord8Loop =
    .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 8])) memeqWord8Step := by rfl

theorem memeq_word32_step_advances : ReadCheckAdvanceStep (ofString "i") 32 memeqWord32Step := by
  repeat first | exact ReadCheckAdvanceStep.advance | apply ReadCheckAdvanceStep.check

theorem memeq_word8_step_advances : ReadCheckAdvanceStep (ofString "i") 8 memeqWord8Step := by
  repeat first | exact ReadCheckAdvanceStep.advance | apply ReadCheckAdvanceStep.check

#print axioms source_memeq_word32_loop
#print axioms source_memeq_word8_loop
#print axioms memeq_word32_step_advances
#print axioms memeq_word8_step_advances
end InitECandidate.Runtime
