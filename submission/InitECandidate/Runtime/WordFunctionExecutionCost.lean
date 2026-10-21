import InitECandidate.Runtime.WordExecutionCostProps
import InitECandidate.Runtime.WordCallLabel
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Executed Word work with function-indexed local prices. Structural children,
continuations and handlers retain the caller identity; an actual callee uses
the label resolved before callEnv discards the indirect function pointer.
This permits per-function colouring prices without conflating reused virtual
register numbers. Uniform prices specialize to the existing counter below. -/
noncomputable def wordFunctionExecutionCost {width : Nat} [NeZero width] {C F : Type}
    (price : Nat → WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (function : Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  match p with
  | .mustTerminate body => price function p s +
      if _hz : s.termdep = 0 then 0
      else wordFunctionExecutionCost price function body { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }
  | .seq first second =>
      let firstWork := wordFunctionExecutionCost price function first s
      match _h : fixClock s (evaluate first s) with
      | (result, middle) => price function p s + firstWork +
          match (generalizing := false) result with
          | none => wordFunctionExecutionCost price function second middle
          | _ => 0
  | .ite cmp reg operand first second => price function p s +
      match getVar reg s, getVarImm operand s with
      | some x, some y => match wordSemWordCmp cmp x y with
        | some true => wordFunctionExecutionCost price function first s
        | some false => wordFunctionExecutionCost price function second s
        | none => 0
      | _, _ => 0
  | .loop names body exitNames =>
      match _hs : cutState (names, .ln) s with
      | none => price function p s
      | some cutSource =>
          let bodyWork := wordFunctionExecutionCost price function body cutSource
          match _h : fixClock cutSource (evaluate body cutSource) with
          | (result, middle) =>
              price function p s + bodyWork + if wordSemContLoop result then
                (if _hc : middle.clock = 0 then 0
                 else wordFunctionExecutionCost price function (wordSemSTOP (.loop names body exitNames)) (Flapjack.WordSemStateFiniteExact.decClock middle))
              else 0
  | .call ret dest args handler =>
      match (generalizing := false) getVars args s with
      | none => price function p s
      | some xs =>
          if wordSemBadDestArgs dest args then price function p s else
          match (generalizing := false) wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
          | none => price function p s
          | some (args1, prog, ss) =>
              let calleeLabel := (wordCallLabel dest (wordSemAddRetLoc ret xs)).getD 0
              match (generalizing := false) ret with
              | none =>
                  match (generalizing := false) handler with
                  | some _ => price function p s
                  | none => if _hc : s.clock = 0 then price function p s
                      else price function p s + wordFunctionExecutionCost price calleeLabel prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (Flapjack.WordSemStateFiniteExact.decClock s))
              | some (values, names, retCode, l1, l2) =>
                  if sptDomainEmpty names.1 ∨ ¬ values.Nodup then price function p s else
                  match (generalizing := false) wordSemCutEnvs names s.locals with
                  | none => price function p s
                  | some envs =>
                      if _hc : s.clock = 0 then price function p s else
                      let bodyWork := wordFunctionExecutionCost price calleeLabel prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                      match _h : fixClock (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                          (evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))) with
                      | (some (.result location returned), middle) =>
                          price function p s + bodyWork + if location ≠ .loc l1 l2 ∨ returned.length ≠ values.length then 0 else
                            match (generalizing := false) _hp : popEnv middle with
                            | none => 0
                            | some popped =>
                                if sptDomainEqUnion popped.locals envs.1 envs.2 then
                                  wordFunctionExecutionCost price function retCode (Flapjack.WordSemStateFiniteExact.setVars values returned popped)
                                else 0
                      | (some (.exception location value), middle) =>
                          price function p s + bodyWork + match (generalizing := false) handler with
                            | none => 0
                            | some (reg, handlerCode, h1, h2) =>
                                if location ≠ .loc h1 h2 then 0 else
                                if sptDomainEqUnion middle.locals envs.1 envs.2 then
                                  wordFunctionExecutionCost price function handlerCode (Flapjack.WordSemStateFiniteExact.setVar reg value middle)
                                else 0
                      | _ => price function p s + bodyWork
  | _ => price function p s
termination_by (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (have hfc := fixClock_IMP_LESS_EQ _ _ _ _ _h)
    try (have hcs := cutState_clock_termdep _ _ _ _hs)
    try (have hpc := popEnv_clock _ _ _hp)
    try (have hpt := popEnv_termdep _ _ _hp)
    try simp only [Flapjack.WordSemStateFiniteExact.callEnv, Flapjack.WordSemStateFiniteExact.decClock, Flapjack.WordSemStateFiniteExact.setVars, Flapjack.WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep,
      wordSemSTOP, true_and] at *
    omega

/-- The new function identity is a conservative costing extension: ignoring
it gives exactly the previously checked actual-execution counter. -/
theorem wordFunctionExecutionCost_uniform {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (function : Nat) (program : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordFunctionExecutionCost (fun _ => price) function program source = wordExecutionCost price program source := by
  classical
  fun_induction wordFunctionExecutionCost (fun _ => price) function program source <;>
    (try simp_all +zetaDelta [wordExecutionCost,wordFunctionExecutionCost])
  all_goals grind (splits := 40) only

/-- Sequencing never changes the current function identity. -/
theorem wordFunctionExecutionCost_seq {width : Nat} [NeZero width] {C F : Type}
    (price : Nat → WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (function : Nat) (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordFunctionExecutionCost price function (.seq first second) source =
      price function (.seq first second) source + wordFunctionExecutionCost price function first source +
        (match evaluate first source with
        | (none,middle) => wordFunctionExecutionCost price function second middle
        | _ => 0) := by
  rw [wordFunctionExecutionCost,fix_clock_evaluate]
  cases run : evaluate first source with
  | mk result middle => cases result <;> rfl

#print axioms wordFunctionExecutionCost
#print axioms wordFunctionExecutionCost_uniform
#print axioms wordFunctionExecutionCost_seq
end InitECandidate.Runtime.FineCost
