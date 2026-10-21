import InitECandidate.Runtime.FullSSACodeTable
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 2000000

/-- Moves read only locals and update only locals. Their complete execution,
including failure, commutes with an arbitrary code-table replacement. -/
theorem word_move_code_frame {C F : Type} (priority : Nat) (pairs : List (Nat × Nat))
    (state : WordSemStateFiniteExact 64 C F) (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    evaluate (.move priority pairs) {state with code := code} =
      ((evaluate (.move priority pairs) state).1,{(evaluate (.move priority pairs) state).2 with code := code}) := by
  have read : getVars (pairs.map Prod.snd) {state with code := code} = getVars (pairs.map Prod.snd) state :=
    (getVars_congr {state with code := code} state rfl (pairs.map Prod.snd)).symm
  simp only [evaluate,read]
  by_cases distinct : (pairs.map Prod.fst).Nodup
  · simp only [if_pos distinct]
    cases getVars (pairs.map Prod.snd) state <;> rfl
  · simp only [if_neg distinct]

#print axioms word_move_code_frame
end InitECandidate.Runtime.FineCost
