import InitECandidate.Runtime.WordPathWork
import InitECandidate.Runtime.LoopToWordExpressionWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Price-parametric execution work of the actual Word run. Structural nodes
may have zero local price. Every reached body/handler/continuation is exposed;
MustTerminate also charges its actual term-depth-decremented body. This is a
runtime cost model, separate from the older additional-Stack-clock budget.
Native bounds must justify the selected local price, not assume this counter
is already a RISC-V instruction count. -/
noncomputable def wordExecutionCost {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  match p with
  | .mustTerminate body => price p s +
      if _hz : s.termdep = 0 then 0
      else wordExecutionCost price body { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }
  | .seq first second =>
      let firstWork := wordExecutionCost price first s
      match _h : fixClock s (evaluate first s) with
      | (result, middle) => price p s + firstWork +
          match (generalizing := false) result with
          | none => wordExecutionCost price second middle
          | _ => 0
  | .ite cmp reg operand first second => price p s +
      match getVar reg s, getVarImm operand s with
      | some x, some y => match wordSemWordCmp cmp x y with
        | some true => wordExecutionCost price first s
        | some false => wordExecutionCost price second s
        | none => 0
      | _, _ => 0
  | .loop names body exitNames =>
      match _hs : cutState (names, .ln) s with
      | none => price p s
      | some cutSource =>
          let bodyWork := wordExecutionCost price body cutSource
          match _h : fixClock cutSource (evaluate body cutSource) with
          | (result, middle) =>
              price p s + bodyWork + if wordSemContLoop result then
                (if _hc : middle.clock = 0 then 0
                 else wordExecutionCost price (wordSemSTOP (.loop names body exitNames)) (Flapjack.WordSemStateFiniteExact.decClock middle))
              else 0
  | .call ret dest args handler =>
      match (generalizing := false) getVars args s with
      | none => price p s
      | some xs =>
          if wordSemBadDestArgs dest args then price p s else
          match (generalizing := false) wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
          | none => price p s
          | some (args1, prog, ss) =>
              match (generalizing := false) ret with
              | none =>
                  match (generalizing := false) handler with
                  | some _ => price p s
                  | none => if _hc : s.clock = 0 then price p s
                      else price p s + wordExecutionCost price prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (Flapjack.WordSemStateFiniteExact.decClock s))
              | some (values, names, retCode, l1, l2) =>
                  if sptDomainEmpty names.1 ∨ ¬ values.Nodup then price p s else
                  match (generalizing := false) wordSemCutEnvs names s.locals with
                  | none => price p s
                  | some envs =>
                      if _hc : s.clock = 0 then price p s else
                      let bodyWork := wordExecutionCost price prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                      match _h : fixClock (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
                          (evaluate prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))) with
                      | (some (.result location returned), middle) =>
                          price p s + bodyWork + if location ≠ .loc l1 l2 ∨ returned.length ≠ values.length then 0 else
                            match (generalizing := false) _hp : popEnv middle with
                            | none => 0
                            | some popped =>
                                if sptDomainEqUnion popped.locals envs.1 envs.2 then
                                  wordExecutionCost price retCode (Flapjack.WordSemStateFiniteExact.setVars values returned popped)
                                else 0
                      | (some (.exception location value), middle) =>
                          price p s + bodyWork + match (generalizing := false) handler with
                            | none => 0
                            | some (reg, handlerCode, h1, h2) =>
                                if location ≠ .loc h1 h2 then 0 else
                                if sptDomainEqUnion middle.locals envs.1 envs.2 then
                                  wordExecutionCost price handlerCode (Flapjack.WordSemStateFiniteExact.setVar reg value middle)
                                else 0
                      | _ => price p s + bodyWork
  | _ => price p s
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

/-- Logical local work, with free structural composition and explicit
expression/move sizes. This instance is not yet a native coefficient table. -/
def wordLogicalPrice {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (_s : WordSemStateFiniteExact 64 C F) : Nat :=
  match p with
  | .skip | .seq _ _ => 0
  | .move _ moves => 1 + moves.length
  | .assign _ value | .set _ value | .store value _ | .shareInst _ _ value =>
      1 + wordExpressionWork value
  | .storeConsts _ _ _ _ words => 1 + words.length
  | .return _ values => 1 + values.length
  | .call _ _ arguments _ => 1 + arguments.length
  | _ => 1

#print axioms wordExecutionCost
end InitECandidate.Runtime.FineCost
