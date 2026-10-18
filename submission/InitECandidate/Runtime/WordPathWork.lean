import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Selected-path WordToStack budget: identical to wordWork except that a
conditional charges only the branch selected by the actual operands.
Conservative budget for quantitative WordToStack simulation, following
actual source successor states. MustTerminate costs one because the compiler
relation excludes its nonzero term-depth branch; this is not a general exact
count of WordSem evaluation nodes. -/
noncomputable def wordPathWork {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  match p with
  | .seq first second =>
      let firstWork := wordPathWork first s
      match _h : fixClock s (evaluate first s) with
      | (result, middle) => 1 + firstWork +
          match (generalizing := false) result with
          | none => wordPathWork second middle
          | _ => 0
  | .ite cmp reg operand first second => 1 +
      match getVar reg s, getVarImm operand s with
      | some x, some y => match wordSemWordCmp cmp x y with
        | some true => wordPathWork first s
        | some false => wordPathWork second s
        | none => 0
      | _, _ => 0
  | .loop names body exitNames =>
      match _hs : cutState (names, .ln) s with
      | none => 1
      | some cutSource =>
          let bodyWork := wordPathWork body cutSource
          match _h : fixClock cutSource (evaluate body cutSource) with
          | (result, middle) =>
              1 + bodyWork + if wordSemContLoop result then
                (if _hc : middle.clock = 0 then 0
                 else wordPathWork (wordSemSTOP (.loop names body exitNames)) (Flapjack.WordSemStateFiniteExact.decClock middle))
              else 0
  | .call ret dest args handler =>
      match (generalizing := false) getVars args s with
      | none => 1
      | some xs =>
          if wordSemBadDestArgs dest args then 1 else
          match (generalizing := false) wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
          | none => 1
          | some (args1, prog, ss) =>
              match (generalizing := false) ret with
              | none =>
                  match (generalizing := false) handler with
                  | some _ => 1
                  | none => if _hc : s.clock = 0 then 1
                      else 1 + wordPathWork prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (Flapjack.WordSemStateFiniteExact.decClock s))
              | some (values, names, retCode, l1, l2) =>
                  if sptDomainEmpty names.1 ∨ ¬ values.Nodup then 1 else
                  match (generalizing := false) wordSemCutEnvs names s.locals with
                  | none => 1
                  | some envs =>
                      if _hc : s.clock = 0 then 1 else
                      let bodyWork := wordPathWork prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                      match _h : fixClock (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                          (evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))) with
                      | (some (.result location returned), middle) =>
                          1 + bodyWork + if location ≠ .loc l1 l2 ∨ returned.length ≠ values.length then 0 else
                            match (generalizing := false) _hp : popEnv middle with
                            | none => 0
                            | some popped =>
                                if sptDomainEqUnion popped.locals envs.1 envs.2 then
                                  wordPathWork retCode (Flapjack.WordSemStateFiniteExact.setVars values returned popped)
                                else 0
                      | (some (.exception location value), middle) =>
                          1 + bodyWork + match (generalizing := false) handler with
                            | none => 0
                            | some (reg, handlerCode, h1, h2) =>
                                if location ≠ .loc h1 h2 then 0 else
                                if sptDomainEqUnion middle.locals envs.1 envs.2 then
                                  wordPathWork handlerCode (Flapjack.WordSemStateFiniteExact.setVar reg value middle)
                                else 0
                      | _ => 1 + bodyWork
  | _ => 1
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

theorem one_le_wordPathWork {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    1 ≤ wordPathWork p s := by
  cases p <;> rw [wordPathWork]
  all_goals try simp
  all_goals repeat' first | omega | split

#print axioms one_le_wordPathWork
#print axioms wordPathWork
end InitECandidate.Runtime.WordToStack
