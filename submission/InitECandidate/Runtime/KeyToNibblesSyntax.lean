import InitECandidate.Runtime.ByteStraightLine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keyToNibblesMainLoop : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_key_to_nibbles with
  | .dec _ _ _ (.seq loop _) => loop
  | _ => .skip

def keyToNibblesTailLoop : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_key_to_nibbles with
  | .dec _ _ _ (.seq _ (.seq loop _)) => loop
  | _ => .skip

def keyToNibblesMainStep : ProgHOL 64 :=
  match keyToNibblesMainLoop with
  | .while _ body => body
  | _ => .skip

def keyToNibblesTailStep : ProgHOL 64 :=
  match keyToNibblesTailLoop with
  | .while _ body => body
  | _ => .skip

theorem source_keyToNibbles_body : sourceFunctionBody Guest.guestFn_key_to_nibbles =
    .dec (ofString "i") .one (.const 0)
      (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))) := by
  simp only [keyToNibblesMainLoop,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_keyToNibbles_main_loop : keyToNibblesMainLoop =
    .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"),.const 4])) keyToNibblesMainStep := by
  simp only [keyToNibblesMainLoop,keyToNibblesMainStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_keyToNibbles_tail_loop : keyToNibblesTailLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) keyToNibblesTailStep := by
  simp only [keyToNibblesTailLoop,keyToNibblesTailStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem keyToNibbles_main_step_straightLine : byteStraightLine keyToNibblesMainStep = true := by
  simp only [keyToNibblesMainStep,keyToNibblesMainLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem keyToNibbles_tail_step_straightLine : byteStraightLine keyToNibblesTailStep = true := by
  simp only [keyToNibblesTailStep,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The eight byte writes of a four-byte step and the two writes of a tail
step consume no nested source fuel, even on a byte load/store failure. -/
theorem evaluate_keyToNibbles_steps_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state keyToNibblesMainStep).2.clock = state.clock ∧
    (evaluateHOLFiniteState state keyToNibblesTailStep).2.clock = state.clock :=
  ⟨clockPreserving_of_byteStraightLine _ keyToNibbles_main_step_straightLine state,
   clockPreserving_of_byteStraightLine _ keyToNibbles_tail_step_straightLine state⟩

theorem evaluate_keyToNibbles_steps_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state keyToNibblesMainStep).1 ≠ some .timeOut ∧
    (evaluateHOLFiniteState state keyToNibblesTailStep).1 ≠ some .timeOut :=
  ⟨evaluate_byteStraightLine_no_timeout _ keyToNibbles_main_step_straightLine state,
   evaluate_byteStraightLine_no_timeout _ keyToNibbles_tail_step_straightLine state⟩

#print axioms source_keyToNibbles_body
#print axioms source_keyToNibbles_main_loop
#print axioms source_keyToNibbles_tail_loop
#print axioms keyToNibbles_main_step_straightLine
#print axioms keyToNibbles_tail_step_straightLine
#print axioms evaluate_keyToNibbles_steps_clock
#print axioms evaluate_keyToNibbles_steps_no_timeout
end InitECandidate.Runtime
