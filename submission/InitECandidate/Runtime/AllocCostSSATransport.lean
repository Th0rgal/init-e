/-
# Work transport along permuted stacks (`PERM_STACK`)

`wordPathWork` counts the executed nodes of the selected path.  The SSA
correctness relation fixes the source permutation existentially, so the executed
work must be shown invariant when the source state's `permute` oracle and stack
roots are replaced by a `PERM_STACK`-related variant.  This module proves the
first slice of that transport: the leaf (`mustTerminate`) case, the sequence
step and the conditional step.  The step lemmas are stated with the transported
work of the sub-programs as explicit hypotheses, i.e. exactly the premises a
termination-measure recursion (mirroring `WordSemStateFiniteExact.swap_aux`)
passes to its induction hypotheses; the actual sub-runs are those of the real
program, so no whole-program evaluation premise is assumed.

The remaining step cases (`.loop`, `.call`) and the recursive driver are the
next slice; the SSA call transfer already leaves only this permute bookkeeping.
-/
import InitECandidate.Runtime.AllocCostSSABodyWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open InitECandidate.Runtime.WordToStack
set_option maxHeartbeats 400000


theorem wordPathWork_mustTerminate_variant{C F : Type} (c : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64)) :
    wordPathWork (.mustTerminate c) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.mustTerminate c) s := by
  rw [wordPathWork, wordPathWork]
  all_goals simp

theorem wordPathWork_seq_variant{C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (res : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F)
    (k1 : Nat → Nat → Nat) (xs1 : List (WordSemStackFrame 64))
    (runS : evaluate first s = (res, s1))
    (runT : evaluate first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = (res, { s1 with permute := k1, stack := xs1 }))
    (ih1 : wordPathWork first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork first s)
    (ih2 : wordPathWork second ({ s1 with permute := k1, stack := xs1 } :
      WordSemStateFiniteExact 64 C F) = wordPathWork second s1) :
    wordPathWork (.seq first second) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.seq first second) s := by
  rw [wordPathWork_seq, wordPathWork_seq]
  rw [runT, runS]
  rw [ih1]
  cases res with
  | none => dsimp only; rw [ih2]
  | some r => rfl

theorem wordPathWork_ite_variant{C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (ih1 : wordPathWork first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork first s)
    (ih2 : wordPathWork second ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork second s) :
    wordPathWork (.ite cmp reg operand first second) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) =
      wordPathWork (.ite cmp reg operand first second) s := by
  have hv : getVar reg ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = getVar reg s := rfl
  have hi : getVarImm operand ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = getVarImm operand s := by
    cases operand <;> rfl
  rw [wordPathWork, wordPathWork, hv, hi]
  cases hx : getVar reg s with
  | none => simp only [hx]
  | some x =>
    cases hy : getVarImm operand s with
    | none => simp only [hx, hy]
    | some y =>
      cases hc : wordSemWordCmp cmp x y with
      | none => simp only [hx, hy, hc]
      | some b =>
        cases b with
        | true => simp only [hx, hy, hc]; rw [ih1]
        | false => simp only [hx, hy, hc]; rw [ih2]


/-- Non-returning call step: the same `getVars`/`findCode` selection is read at
the variant state, and the compiled-free call node plus the callee body's
transported work at the literal `callEnv` entry gives the same total. -/
theorem wordPathWork_call_none_variant {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (values : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some values)
    (hbad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) values) s.code s.stackSize =
      some (args1, prog, ss))
    (hz : s.clock ≠ 0)
    (ih : wordPathWork prog (callEnv args1 ss (decClock ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F))) = wordPathWork prog (callEnv args1 ss (decClock s))) :
    wordPathWork (.call none dest args none) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.call none dest args none) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some values := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) values)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hzT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := hz
  rw [wordPathWork_call_none_body_eq dest args ({ s with permute := k, stack := xs })
      values args1 prog ss hgetT hbad hfindT hzT,
    wordPathWork_call_none_body_eq dest args s values args1 prog ss get hbad find hz, ih]

/-- Returning call, `result` branch: the variant reads the same arguments,
uses the same code and cut environments, the body's actual transported run
returns the same result, its environment pops to a `PERM_STACK`-related frame,
and both the body work and the return-handler work transfer. -/
theorem wordPathWork_call_returning_result_variant {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (vals0 : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle middleX : WordSemStateFiniteExact 64 C F)
    (popped : WordSemStateFiniteExact 64 C F)
    (k3 : Nat → Nat → Nat) (xs3 : List (WordSemStackFrame 64))
    (get : getVars args s = some vals0)
    (hbad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (runS : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (some (.result location returned), middle))
    (popS : popEnv middle = some popped)
    (locEq : location = .loc l1 l2)
    (lenEq : returned.length = values.length)
    (domUnion : sptDomainEqUnion popped.locals envs.1 envs.2)
    (runT : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      (some (.result location returned), middleX))
    (popT : popEnv middleX = some ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F))
    (ihBody : wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))))
    (ihRet : wordPathWork retCode ({ setVars values returned popped with
      permute := k3, stack := xs3 } : WordSemStateFiniteExact 64 C F) =
      wordPathWork retCode (setVars values returned popped)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some vals0 := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hcutT : wordSemCutEnvs names ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).locals = some envs := cut
  have hclockT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := clock
  have hdomUnionT : sptDomainEqUnion ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F).locals envs.1 envs.2 := domUnion
  have hsv : setVars values returned ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F) =
      ({ setVars values returned popped with permute := k3, stack := xs3 } :
        WordSemStateFiniteExact 64 C F) := rfl
  rw [wordPathWork_call_returning_result values names retCode l1 l2 dest args handler
      ({ s with permute := k, stack := xs }) middleX
      ({ popped with permute := k3, stack := xs3 }) vals0 envs args1 prog ss location returned
      hgetT hbad hfindT dom nodup hcutT hclockT (by rw [fix_clock_evaluate]; exact runT)
      popT locEq lenEq hdomUnionT,
    wordPathWork_call_returning_result values names retCode l1 l2 dest args handler s middle
      popped vals0 envs args1 prog ss location returned get hbad find dom nodup cut clock
      (by rw [fix_clock_evaluate]; exact runS) popS locEq lenEq domUnion]
  rw [hsv, ihBody, ihRet]


/-- Non-dependent unfolding of `wordPathWork` at a loop: the cut state and the
body's raw `evaluate` result are exposed (the `fixClock` wrapper is removed by
`fix_clock_evaluate`), keeping the actual `cutState`/`contLoop`/clock guards as
equation guards.  This is the loop analogue of `wordPathWork_seq`. -/
theorem wordPathWork_loop {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec width))
    (exitNames : WordLangNumSetHOL) (s : WordSemStateFiniteExact width C F) :
    wordPathWork (.loop names body exitNames) s =
      match cutState (names, .ln) s with
      | none => 1
      | some cutSource =>
          1 + wordPathWork body cutSource +
            (match evaluate body cutSource with
             | (result, middle) =>
                if wordSemContLoop result then
                  (if _hc : middle.clock = 0 then 0
                   else wordPathWork (wordSemSTOP (.loop names body exitNames))
                     (decClock middle))
                else 0) := by
  rw [wordPathWork]
  all_goals try simp
  cases hs : cutState (names, .ln) s with
  | none => rfl
  | some cs =>
      dsimp only
      rw [fix_clock_evaluate]
      try (cases run : evaluate body cs with
        | mk result middle =>
            dsimp only
            rfl)

/-- Loop step of the work transport: the cut state transports pointwise, the
body's actual transported run returns the same result, and the STOP self-call
transports at the decremented clock (both are induction hypotheses of the
driver).  The `contLoop` guard and the clock guard read the same values. -/
theorem wordPathWork_loop_variant {C F : Type}
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (exitNames : WordLangNumSetHOL) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (cs : WordSemStateFiniteExact 64 C F)
    (hcs : cutState (names, .ln) s = some cs)
    (hcsT : cutState (names, .ln) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some ({ cs with permute := k, stack := xs } :
        WordSemStateFiniteExact 64 C F))
    (res : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F)
    (k1 : Nat → Nat → Nat) (xs1 : List (WordSemStackFrame 64))
    (runS : evaluate body cs = (res, s1))
    (runT : evaluate body ({ cs with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = (res, { s1 with permute := k1, stack := xs1 }))
    (ihBody : wordPathWork body ({ cs with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork body cs)
    (ihStop : s1.clock ≠ 0 → wordPathWork (.loop names body exitNames)
      ({ decClock s1 with permute := k1, stack := xs1 } : WordSemStateFiniteExact 64 C F) =
      wordPathWork (.loop names body exitNames) (decClock s1)) :
    wordPathWork (.loop names body exitNames) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) =
      wordPathWork (.loop names body exitNames) s := by
  have hclock : ({ s1 with permute := k1, stack := xs1 } :
      WordSemStateFiniteExact 64 C F).clock = s1.clock := rfl
  have hdec : decClock ({ s1 with permute := k1, stack := xs1 } :
      WordSemStateFiniteExact 64 C F) =
      ({ decClock s1 with permute := k1, stack := xs1 } :
        WordSemStateFiniteExact 64 C F) := rfl
  rw [wordPathWork_loop, wordPathWork_loop, hcsT, hcs]
  dsimp only
  rw [runT, runS, ihBody, hclock, hdec]
  simp only [wordSemSTOP]
  by_cases hc : wordSemContLoop res
  · rw [if_pos hc, if_pos hc]
    by_cases hz : s1.clock = 0
    · rw [dif_pos hz, dif_pos hz]
    · rw [dif_neg hz, dif_neg hz, ihStop hz]
  · rw [if_neg hc, if_neg hc]


/-! ### Returning calls: exception and terminal branches -/

/-- Returning call whose callee raises an exception that the handler catches:
one call node, the callee BODY work and the handler work at the actual
post-call state. -/
theorem wordPathWork_call_returning_exception {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location value : WordLocW 64)
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.exception location value), middle))
    (handl : handler = some (reg, handlerCode, h1, h2))
    (locEq : location = .loc h1 h2)
    (domUnion : sptDomainEqUnion middle.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) +
        wordPathWork handlerCode (setVar reg value middle) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [handl]
  dsimp only
  rw [if_neg (by simp [locEq]), if_pos domUnion]

/-- Returning call whose callee result is neither a `result` nor an
`exception`: the call falls through to the terminal branch and costs one node
plus the callee body work. -/
theorem wordPathWork_call_returning_other {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (result : Option (WordSemResult 64))
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (result, middle))
    (hnotRes : ∀ (l : WordLocW 64) (r : List (WordLocW 64)), result ≠ some (.result l r))
    (hnotExc : ∀ (l v : WordLocW 64), result ≠ some (.exception l v)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  cases result with
  | none => rfl
  | some r =>
      cases r with
      | result l rr => exact absurd rfl (hnotRes l rr)
      | exception l v => exact absurd rfl (hnotExc l v)
      | _ => rfl

/-- Transport of the exception branch of a returning call. -/
theorem wordPathWork_call_returning_exception_variant {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (vals0 : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (k2 : Nat → Nat → Nat) (xs2 : List (WordSemStackFrame 64))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (get : getVars args s = some vals0)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (runS : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (some (.exception location value), middle))
    (handl : handler = some (reg, handlerCode, h1, h2))
    (locEq : location = .loc h1 h2)
    (domUnion : sptDomainEqUnion middle.locals envs.1 envs.2)
    (runT : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      (some (.exception location value), ({ middle with permute := k2, stack := xs2 } :
        WordSemStateFiniteExact 64 C F)))
    (ihBody : wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))))
    (ihHandler : wordPathWork handlerCode ({ setVar reg value middle with
      permute := k2, stack := xs2 } : WordSemStateFiniteExact 64 C F) =
      wordPathWork handlerCode (setVar reg value middle)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some vals0 := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hcutT : wordSemCutEnvs names ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).locals = some envs := cut
  have hclockT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := clock
  have hdomUnionT : sptDomainEqUnion ({ middle with permute := k2, stack := xs2 } :
      WordSemStateFiniteExact 64 C F).locals envs.1 envs.2 := domUnion
  have hsv : setVar reg value ({ middle with permute := k2, stack := xs2 } :
      WordSemStateFiniteExact 64 C F) =
      ({ setVar reg value middle with permute := k2, stack := xs2 } :
        WordSemStateFiniteExact 64 C F) := rfl
  rw [wordPathWork_call_returning_exception values names retCode l1 l2 dest args handler
      ({ s with permute := k, stack := xs }) ({ middle with permute := k2, stack := xs2 })
      vals0 envs args1 prog ss location value reg handlerCode h1 h2
      hgetT bad hfindT dom nodup hcutT hclockT (by rw [fix_clock_evaluate]; exact runT)
      handl locEq hdomUnionT,
    wordPathWork_call_returning_exception values names retCode l1 l2 dest args handler
      s middle vals0 envs args1 prog ss location value reg handlerCode h1 h2
      get bad find dom nodup cut clock (by rw [fix_clock_evaluate]; exact runS)
      handl locEq domUnion]
  rw [hsv, ihBody, ihHandler]

/-- Transport of the terminal branch of a returning call. -/
theorem wordPathWork_call_returning_other_variant {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (vals0 : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (result : Option (WordSemResult 64)) (middle middleT : WordSemStateFiniteExact 64 C F)
    (get : getVars args s = some vals0)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (runS : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (result, middle))
    (hnotRes : ∀ (l : WordLocW 64) (r : List (WordLocW 64)), result ≠ some (.result l r))
    (hnotExc : ∀ (l v : WordLocW 64), result ≠ some (.exception l v))
    (runT : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      (result, middleT))
    (ihBody : wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some vals0 := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hcutT : wordSemCutEnvs names ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).locals = some envs := cut
  have hclockT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := clock
  rw [wordPathWork_call_returning_other values names retCode l1 l2 dest args handler
      ({ s with permute := k, stack := xs }) middleT vals0 envs args1 prog ss result
      hgetT bad hfindT dom nodup hcutT hclockT (by rw [fix_clock_evaluate]; exact runT)
      hnotRes hnotExc,
    wordPathWork_call_returning_other values names retCode l1 l2 dest args handler
      s middle vals0 envs args1 prog ss result get bad find dom nodup cut clock
      (by rw [fix_clock_evaluate]; exact runS) hnotRes hnotExc]
  rw [ihBody]

#print axioms wordPathWork_loop
#print axioms wordPathWork_loop_variant
#print axioms wordPathWork_call_returning_exception
#print axioms wordPathWork_call_returning_other
#print axioms wordPathWork_call_returning_exception_variant
#print axioms wordPathWork_call_returning_other_variant

/-! ### Terminal call paths, structure-exposing call lemma, and the driver -/

/-- Any call whose argument read fails costs one node. -/
theorem wordPathWork_call_getVars_none {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (get : getVars args s = none) :
    wordPathWork (.call ret dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get]

/-- Any call with a bad destination/argument shape costs one node. -/
theorem wordPathWork_call_badDest {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (get : getVars args s = some xs) (bad : wordSemBadDestArgs dest args = true) :
    wordPathWork (.call ret dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad]

/-- Any call whose code lookup fails costs one node. -/
theorem wordPathWork_call_findCode_none {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (get : getVars args s = some xs) (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = none) :
    wordPathWork (.call ret dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find]

/-- A returning call with a trivial cut-set name domain costs one node. -/
theorem wordPathWork_call_returning_dom {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some xs) (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (hdom : sptDomainEmpty names.1 ∨ ¬ values.Nodup) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find, hdom]

/-- A returning call whose cut-set environment lookup fails costs one node. -/
theorem wordPathWork_call_returning_cut_none {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some xs) (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (hcut : wordSemCutEnvs names s.locals = none) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find, dom, nodup, hcut]

/-- A returning call at zero clock costs one node. -/
theorem wordPathWork_call_returning_clock_zero {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some xs) (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock = 0) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s = 1 := by
  rw [wordPathWork]
  simp [get, bad, find, dom, nodup, cut, clock]


/-- Fall-through of a returning call whose result lists do not line up: one
node plus the callee body work. -/
theorem wordPathWork_call_returning_result_fall {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.result location returned), middle))
    (hfall : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [if_pos hfall]
  omega

/-- Fall-through of a returning call whose environment pop fails. -/
theorem wordPathWork_call_returning_result_pop_none {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.result location returned), middle))
    (popS : popEnv middle = none)
    (locEq : location = .loc l1 l2) (lenEq : returned.length = values.length) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [if_neg (by simp [locEq, lenEq])]
  split <;> simp_all

/-- Fall-through of a returning call whose return environment is not related
to the cut environments. -/
theorem wordPathWork_call_returning_result_union_false {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle popped : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.result location returned), middle))
    (popS : popEnv middle = some popped)
    (locEq : location = .loc l1 l2) (lenEq : returned.length = values.length)
    (hunion : ¬ sptDomainEqUnion popped.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [if_neg (by simp [locEq, lenEq])]
  split <;> simp_all

/-- Fall-through of a returning call whose exception has no handler. -/
theorem wordPathWork_call_returning_exception_unhandled {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location value : WordLocW 64)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.exception location value), middle))
    (handl : handler = none) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [handl]
  try dsimp only
  omega

/-- Fall-through of a returning call whose exception location does not match
its handler. -/
theorem wordPathWork_call_returning_exception_fall {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location value : WordLocW 64)
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.exception location value), middle))
    (handl : handler = some (reg, handlerCode, h1, h2))
    (hloc : location ≠ .loc h1 h2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [handl]
  try dsimp only
  rw [if_pos hloc]
  omega

/-- Fall-through of a returning call whose handler environment is not related
to the cut environments. -/
theorem wordPathWork_call_returning_exception_union_false {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (location value : WordLocW 64)
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (get : getVars args s = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
      (some (.exception location value), middle))
    (handl : handler = some (reg, handlerCode, h1, h2))
    (locEq : location = .loc h1 h2)
    (hunion : ¬ sptDomainEqUnion middle.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s =
      1 + wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
  rw [wordPathWork]
  simp only [get]
  rw [bad, if_neg (by simp)]
  rw [find]
  dsimp only
  rw [if_neg (by simp [dom, nodup])]
  rw [cut]
  dsimp only
  rw [dif_neg clock]
  rw [run]
  dsimp only
  rw [handl]
  try dsimp only
  rw [if_neg (by simp [locEq])]
  try dsimp only
  rw [if_neg hunion]
  omega

#print axioms wordPathWork_call_getVars_none
#print axioms wordPathWork_call_badDest
#print axioms wordPathWork_call_findCode_none
#print axioms wordPathWork_call_returning_dom
#print axioms wordPathWork_call_returning_cut_none
#print axioms wordPathWork_call_returning_clock_zero
#print axioms wordPathWork_call_returning_result_fall
#print axioms wordPathWork_call_returning_result_pop_none
#print axioms wordPathWork_call_returning_result_union_false
#print axioms wordPathWork_call_returning_exception_unhandled
#print axioms wordPathWork_call_returning_exception_fall
#print axioms wordPathWork_call_returning_exception_union_false
#print axioms wordPathWork_mustTerminate_variant
#print axioms wordPathWork_seq_variant
#print axioms wordPathWork_ite_variant
#print axioms wordPathWork_call_none_variant
#print axioms wordPathWork_call_returning_result_variant

set_option maxHeartbeats 2000000 in
/-- `decClock` commutes syntactically with the oracle/stack substitution. -/
theorem decClock_stack_permute {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64)) :
    decClock ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
      ({ decClock s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) := rfl

set_option maxHeartbeats 2000000 in
/-- **`PERM_STACK` executed-work driver (run transport).**  Replacing the
permutation oracle and the stack roots by a `PERM_STACK`-related stack does not
change the executed work of any program whose subprograms are allocation- and
installation-free and whose code map is.  Each constructor transports the actual
`evaluate` run of its subprograms (`swap_aux`) and consumes the corresponding
checked step lemma at the transported intermediate states; the sub-run equations
are the ones the real program produces, so no evaluation premise is assumed. -/
theorem wordPathWork_permStack_variant {C F : Type} :
    ∀ (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
      (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64)),
      List.Forall₂ permStack xs s.stack →
      noAllocSubprogsHOL p = true → noInstallSubprogsHOL p = true →
      WordProps.noAllocCode s.code → WordProps.noInstallCode s.code →
      wordPathWork p ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
        wordPathWork p s
  | .mustTerminate q, s, k, xs, _, _, _, _, _ => wordPathWork_mustTerminate_variant q s k xs
  | .seq c1 c2, s, k, xs, hxs, hna, hni, hca, hci => by
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      obtain ⟨k1, xs1, he, hrel⟩ := swap_aux c1 s k xs hxs hna.1 hni.1 hca hci
      have hcode := code_evaluate c1 s hni.1 hci
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      have hfix : fixClock s (evaluate c1 s) = (r1, s1) := by
        simpa only [h1] using fix_clock_evaluate s c1
      have hdecR : s1.clock ≤ s.clock := (fixClock_IMP_LESS_EQ s r1 s1 _ hfix).1
      have hdecT : s1.termdep = s.termdep := (fixClock_IMP_LESS_EQ s r1 s1 _ hfix).2
      rw [h1] at he hrel hcode
      simp only [Prod.fst, Prod.snd] at he
      exact wordPathWork_seq_variant c1 c2 s k xs r1 s1 k1 xs1 h1 he
        (wordPathWork_permStack_variant c1 s k xs hxs hna.1 hni.1 hca hci)
        (wordPathWork_permStack_variant c2 s1 k1 xs1 hrel hna.2 hni.2 (hcode ▸ hca) (hcode ▸ hci))
  | .ite cmp reg operand c1 c2, s, k, xs, hxs, hna, hni, hca, hci => by
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      exact wordPathWork_ite_variant cmp reg operand c1 c2 s k xs
        (wordPathWork_permStack_variant c1 s k xs hxs hna.1 hni.1 hca hci)
        (wordPathWork_permStack_variant c2 s k xs hxs hna.2 hni.2 hca hci)
  | .loop names body exitNames, s, k, xs, hxs, hna0, hni0, hca, hci => by
      have hna := hna0
      have hni := hni0
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      rcases hcs : cutState (names, .ln) s with _ | cs
      · have hcsT : cutState (names, .ln) ({ s with permute := k, stack := xs } :
            WordSemStateFiniteExact 64 C F) = none := by
          rw [cutState_swap s k xs (names, .ln), hcs]; rfl
        rw [wordPathWork, wordPathWork, hcsT, hcs]
      · obtain ⟨l, rfl⟩ := cutStateConst (names, .ln) s cs hcs
        have hcsT : cutState (names, .ln) ({ s with permute := k, stack := xs } :
            WordSemStateFiniteExact 64 C F) =
            some ({ { s with locals := l } with permute := k, stack := xs } :
              WordSemStateFiniteExact 64 C F) := by
          rw [cutState_swap s k xs (names, .ln), hcs]; rfl
        obtain ⟨k1, xs1, he, hrel⟩ := swap_aux body { s with locals := l } k xs hxs hna hni hca hci
        have hcode := code_evaluate body { s with locals := l } hni hci
        rcases hb : evaluate body { s with locals := l } with ⟨rb, s1⟩
        have hfix : fixClock { s with locals := l }
            (evaluate body { s with locals := l }) = (rb, s1) := by
          simpa only [hb] using fix_clock_evaluate { s with locals := l } body
        have hdecR : s1.clock ≤ s.clock := by
          have hbR := (fixClock_IMP_LESS_EQ { s with locals := l } rb s1 _ hfix).1
          have hstep : ({ s with locals := l } : WordSemStateFiniteExact 64 C F).clock = s.clock := rfl
          omega
        have hdecT : s1.termdep = s.termdep := by
          have hbT := (fixClock_IMP_LESS_EQ { s with locals := l } rb s1 _ hfix).2
          have hstep : ({ s with locals := l } : WordSemStateFiniteExact 64 C F).termdep = s.termdep := rfl
          omega
        rw [hb] at he hrel hcode
        simp only [Prod.fst, Prod.snd] at he
        exact wordPathWork_loop_variant names body exitNames s k xs { s with locals := l }
          hcs hcsT rb s1 k1 xs1 hb he
          (wordPathWork_permStack_variant body { s with locals := l } k xs hxs hna hni hca hci)
          (fun _ => wordPathWork_permStack_variant (.loop names body exitNames) (decClock s1)
            k1 xs1 hrel hna0 hni0 (hcode ▸ hca) (hcode ▸ hci))
  | .skip, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .move a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .inst a, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .assign a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .get a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .set a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .store a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .tick, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .storeConsts a b c d e, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .return a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .raise a, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .break a, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .continue a, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .opCurrHeap a b c, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .locValue a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .install a b c d e, s, k, xs, _, _, hni, _, _ => by
      simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni
  | .codeBufferWrite a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .dataBufferWrite a b, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .ffi a b c d e f, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .shareInst a b c, s, k, xs, _, _, _, _, _ => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .alloc a b, s, k, xs, _, hna, _, _, _ => by
      simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at hna
  | .call ret dest args handler, s, k, xs, hxs, hna, hni, hca, hci => by
      classical
      have hgetT : getVars args ({ s with permute := k, stack := xs } :
          WordSemStateFiniteExact 64 C F) = getVars args s := getVars_swap s k xs args
      rcases hg : getVars args s with _ | vals0
      · rw [wordPathWork_call_getVars_none ret dest args handler s hg,
            wordPathWork_call_getVars_none ret dest args handler
              ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)
              (by rw [hgetT]; exact hg)]
      · by_cases hbad : wordSemBadDestArgs dest args = true
        · rw [wordPathWork_call_badDest ret dest args handler s vals0 hg hbad,
              wordPathWork_call_badDest ret dest args handler
                ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) vals0
                (by rw [hgetT]; exact hg) hbad]
        · have hbad' : wordSemBadDestArgs dest args = false := by
            cases h : wordSemBadDestArgs dest args <;> simp_all
          rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret vals0) s.code s.stackSize with
            _ | ⟨args1, prog, ss⟩
          · rw [wordPathWork_call_findCode_none ret dest args handler s vals0 hg hbad' hf,
                wordPathWork_call_findCode_none ret dest args handler
                  ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) vals0
                  (by rw [hgetT]; exact hg) hbad' hf]
          · have hpa := WordProps.noAllocFindCode s.code dest _ _ _ prog _ ⟨hf, hca⟩
            have hpi := WordProps.noInstallFindCode s.code dest _ _ _ prog _ ⟨hci, hf⟩
            cases ret with
            | none =>
                cases handler with
                | some hh =>
                    rw [wordPathWork_call_none_handler dest args hh s hg hbad' hf,
                        wordPathWork_call_none_handler dest args hh
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)
                          (by rw [hgetT]; exact hg) hbad' hf]
                | none =>
                    by_cases hz : s.clock = 0
                    · rw [wordPathWork_call_none_clock_zero dest args s hg hbad' hf hz,
                          wordPathWork_call_none_clock_zero dest args
                            ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)
                            (by rw [hgetT]; exact hg) hbad' hf hz]
                    · have hrel0 : List.Forall₂ permStack xs (callEnv args1 ss (decClock s)).stack := by
                        rw [show (callEnv args1 ss (decClock s)).stack = s.stack from rfl]; exact hxs
                      have hentry : callEnv args1 ss (decClock ({ s with permute := k, stack := xs } :
                          WordSemStateFiniteExact 64 C F)) =
                          { callEnv args1 ss (decClock s) with permute := k, stack := xs } := by
                        rw [show decClock ({ s with permute := k, stack := xs } :
                              WordSemStateFiniteExact 64 C F) =
                              { decClock s with permute := k, stack := xs } from rfl,
                          callEnv_swap (decClock s) k xs hrel0 args1 ss]
                      have hdecR : (callEnv args1 ss (decClock s)).clock < s.clock := by
                        have h2 : (callEnv args1 ss (decClock s)).clock = (decClock s).clock := rfl
                        have h3 : (decClock s).clock = s.clock - 1 := rfl
                        omega
                      have hdecT : (callEnv args1 ss (decClock s)).termdep = s.termdep := by
                        have h2 : (callEnv args1 ss (decClock s)).termdep = (decClock s).termdep := rfl
                        have h3 : (decClock s).termdep = s.termdep := rfl
                        omega
                      have ihB : wordPathWork prog (callEnv args1 ss (decClock
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F))) =
                          wordPathWork prog (callEnv args1 ss (decClock s)) := by
                        rw [hentry]
                        exact wordPathWork_permStack_variant prog (callEnv args1 ss (decClock s))
                          k xs hrel0 hpa hpi hca hci
                      rw [wordPathWork_call_none_body_eq dest args s vals0 args1 prog ss hg hbad' hf hz,
                        wordPathWork_call_none_body_eq dest args
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)
                          vals0 args1 prog ss (by rw [hgetT]; exact hg) hbad' hf hz, ihB]
            | some rv =>
                obtain ⟨values, names, retCode, l1, l2⟩ := rv
                have hra : noAllocSubprogsHOL retCode = true := noAlloc_call_ret hna
                have hri : noInstallSubprogsHOL retCode = true := noInstall_call_ret hni
                by_cases hdom : sptDomainEmpty names.1 ∨ ¬ values.Nodup
                · rw [wordPathWork_call_returning_dom values names retCode l1 l2 dest args handler s
                      vals0 args1 prog ss hg hbad' hf hdom,
                    wordPathWork_call_returning_dom values names retCode l1 l2 dest args handler
                      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) vals0
                      args1 prog ss (by rw [hgetT]; exact hg) hbad' hf hdom]
                · have hdom1 : ¬ sptDomainEmpty names.1 := fun h => hdom (Or.inl h)
                  have hnodup : values.Nodup := by
                    by_contra h; exact hdom (Or.inr h)
                  rcases hc : wordSemCutEnvs names s.locals with _ | envs
                  · rw [wordPathWork_call_returning_cut_none values names retCode l1 l2 dest args
                        handler s vals0 args1 prog ss hg hbad' hf hdom1 hnodup hc,
                      wordPathWork_call_returning_cut_none values names retCode l1 l2 dest args
                        handler ({ s with permute := k, stack := xs } :
                          WordSemStateFiniteExact 64 C F) vals0 args1 prog ss
                        (by rw [hgetT]; exact hg) hbad' hf hdom1 hnodup hc]
                  · by_cases hz : s.clock = 0
                    · rw [wordPathWork_call_returning_clock_zero values names retCode l1 l2 dest args
                          handler s vals0 envs args1 prog ss hg hbad' hf hdom1 hnodup hc hz,
                        wordPathWork_call_returning_clock_zero values names retCode l1 l2 dest args
                          handler ({ s with permute := k, stack := xs } :
                            WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                          (by rw [hgetT]; exact hg) hbad' hf hdom1 hnodup hc hz]
                    · obtain ⟨k1, xs1, hpe, hrel1⟩ := pushEnv_swap (decClock s) k xs hxs envs handler
                      have hpush : pushEnv envs handler (decClock ({ s with permute := k, stack := xs } :
                          WordSemStateFiniteExact 64 C F)) =
                          { pushEnv envs handler (decClock s) with permute := k1, stack := xs1 } := by
                        rw [decClock_stack_permute]
                        exact hpe
                      have hentry : callEnv args1 ss (pushEnv envs handler (decClock
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F))) =
                          { callEnv args1 ss (pushEnv envs handler (decClock s)) with
                            permute := k1, stack := xs1 } := by
                        rw [hpush]
                        exact callEnv_swap (pushEnv envs handler (decClock s)) k1 xs1 hrel1 args1 ss
                      have hcpre : (callEnv args1 ss (pushEnv envs handler (decClock s))).code =
                          s.code := code_pushEnv envs handler _
                      have hdecR : (callEnv args1 ss (pushEnv envs handler (decClock s))).clock <
                          s.clock := by
                        have h1 : (pushEnv envs handler (decClock s)).clock = (decClock s).clock :=
                          pushEnv_clock _ _ _
                        have h2 : (callEnv args1 ss (pushEnv envs handler (decClock s))).clock =
                            (pushEnv envs handler (decClock s)).clock := rfl
                        have h3 : (decClock s).clock = s.clock - 1 := rfl
                        omega
                      have hdecT : (callEnv args1 ss (pushEnv envs handler (decClock s))).termdep =
                          s.termdep := by
                        have h1 : (pushEnv envs handler (decClock s)).termdep =
                            (decClock s).termdep := pushEnv_termdep _ _ _
                        have h2 : (callEnv args1 ss (pushEnv envs handler (decClock s))).termdep =
                            (pushEnv envs handler (decClock s)).termdep := rfl
                        have h3 : (decClock s).termdep = s.termdep := rfl
                        omega
                      have ihB : wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock
                          ({ s with permute := k, stack := xs } :
                            WordSemStateFiniteExact 64 C F)))) =
                          wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))) := by
                        rw [hentry]
                        exact wordPathWork_permStack_variant prog
                          (callEnv args1 ss (pushEnv envs handler (decClock s))) k1 xs1 hrel1 hpa hpi
                          (hcpre ▸ hca) (hcpre ▸ hci)
                      obtain ⟨k2, xs2, hrun, hrel2⟩ := swap_aux prog
                        (callEnv args1 ss (pushEnv envs handler (decClock s))) k1 xs1 hrel1 hpa hpi
                        (hcpre ▸ hca) (hcpre ▸ hci)
                      have hcode2 := code_evaluate prog
                        (callEnv args1 ss (pushEnv envs handler (decClock s))) hpi (hcpre ▸ hci)
                      rcases hcv : evaluate prog
                        (callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨rc, s2⟩
                      rw [hcv] at hrun hrel2 hcode2
                      simp only [Prod.fst, Prod.snd] at hrun
                      have hfixS : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
                          (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) =
                          (rc, s2) := by
                        simpa only [hcv] using fix_clock_evaluate
                          (callEnv args1 ss (pushEnv envs handler (decClock s))) prog
                      have hrunT : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
                          (rc, ({ s2 with permute := k2, stack := xs2 } :
                            WordSemStateFiniteExact 64 C F)) := by
                        rw [hentry]; exact hrun
                      have hfixT : fixClock (callEnv args1 ss (pushEnv envs handler (decClock
                          ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F))))
                          (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
                            ({ s with permute := k, stack := xs } :
                              WordSemStateFiniteExact 64 C F))))) =
                          (rc, ({ s2 with permute := k2, stack := xs2 } :
                            WordSemStateFiniteExact 64 C F)) := by
                        simpa only [hrunT] using fix_clock_evaluate (callEnv args1 ss (pushEnv envs
                          handler (decClock ({ s with permute := k, stack := xs } :
                            WordSemStateFiniteExact 64 C F)))) prog
                      have hdecR2 : s2.clock < s.clock := by
                        have h1 := (fixClock_IMP_LESS_EQ
                          (callEnv args1 ss (pushEnv envs handler (decClock s))) rc s2 _ hfixS).1
                        have h2 : (callEnv args1 ss (pushEnv envs handler (decClock s))).clock =
                            (decClock s).clock := by
                          rw [show (callEnv args1 ss (pushEnv envs handler (decClock s))).clock =
                              (pushEnv envs handler (decClock s)).clock from rfl, pushEnv_clock]
                        have h3 : (decClock s).clock = s.clock - 1 := rfl
                        omega
                      have hdecT2 : s2.termdep = s.termdep := by
                        have h1 := (fixClock_IMP_LESS_EQ
                          (callEnv args1 ss (pushEnv envs handler (decClock s))) rc s2 _ hfixS).2
                        omega
                      cases rc with
                      | none =>
                          rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                              dest args handler s k xs vals0 args1 prog ss envs
                              (none : Option (WordSemResult 64)) s2
                              ({ s2 with permute := k2, stack := xs2 } :
                                WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                              (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                      | some rc =>
                       cases rc with
                        | result location returned =>
                            by_cases hfall : location ≠ .loc l1 l2 ∨
                                returned.length ≠ values.length
                            · rw [wordPathWork_call_returning_result_fall values names retCode l1 l2
                                  dest args handler s s2 vals0 envs args1 prog ss location returned hg
                                  hbad' hf hdom1 hnodup hc hz hfixS hfall,
                                wordPathWork_call_returning_result_fall values names retCode l1 l2
                                  dest args handler
                                  ({ s with permute := k, stack := xs } :
                                    WordSemStateFiniteExact 64 C F)
                                  ({ s2 with permute := k2, stack := xs2 } :
                                    WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                  location returned (by rw [hgetT]; exact hg) hbad' hf hdom1 hnodup hc
                                  hz hfixT hfall, ihB]
                            · have hlocEq : location = .loc l1 l2 := by
                                by_contra h; exact hfall (Or.inl h)
                              have hlenEq : returned.length = values.length := by
                                by_contra h; exact hfall (Or.inr h)
                              rcases hpop : popEnv s2 with _ | popped
                              · have hpopT : popEnv ({ s2 with permute := k2, stack := xs2 } :
                                    WordSemStateFiniteExact 64 C F) = none :=
                                  (popEnv_swap s2 k2 xs2 hrel2).1 hpop
                                rw [wordPathWork_call_returning_result_pop_none values names retCode
                                      l1 l2 dest args handler s s2 vals0 envs args1 prog ss location
                                      returned hg hbad' hf hdom1 hnodup hc hz hfixS hpop hlocEq hlenEq,
                                    wordPathWork_call_returning_result_pop_none values names retCode
                                      l1 l2 dest args handler
                                      ({ s with permute := k, stack := xs } :
                                        WordSemStateFiniteExact 64 C F)
                                      ({ s2 with permute := k2, stack := xs2 } :
                                        WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                      location returned (by rw [hgetT]; exact hg) hbad' hf hdom1
                                      hnodup hc hz hfixT hpopT hlocEq hlenEq, ihB]
                              · obtain ⟨xs3, hpopT, hrel3⟩ :=
                                  (popEnv_swap s2 k2 xs2 hrel2).2 popped hpop
                                by_cases hdu : sptDomainEqUnion popped.locals envs.1 envs.2
                                · have hretR : (setVars values returned popped).clock < s.clock := by
                                    have h1 : (setVars values returned popped).clock = popped.clock := rfl
                                    have h2 : popped.clock = s2.clock := popEnv_clock s2 popped hpop
                                    omega
                                  have hretT : (setVars values returned popped).termdep = s.termdep := by
                                    have h1 : (setVars values returned popped).termdep =
                                        popped.termdep := rfl
                                    have h2 : popped.termdep = s2.termdep :=
                                      popEnv_termdep s2 popped hpop
                                    omega
                                  have hpopCode : popped.code = s2.code := by
                                    have h2 := hpop
                                    unfold popEnv at h2
                                    split at h2 <;> (try cases h2) <;> rfl
                                  have hentryCode :
                                      (callEnv args1 ss (pushEnv envs handler (decClock s))).code =
                                        s.code := by
                                    rw [show (callEnv args1 ss (pushEnv envs handler (decClock s))).code =
                                        (pushEnv envs handler (decClock s)).code from rfl,
                                      code_pushEnv]
                                    rfl
                                  have hretCode : (setVars values returned popped).code = s.code := by
                                    rw [show (setVars values returned popped).code = popped.code from rfl]
                                    exact (hpopCode.trans hcode2).trans hentryCode
                                  have ihRet : wordPathWork retCode ({ setVars values returned popped with
                                      permute := k2, stack := xs3 } :
                                        WordSemStateFiniteExact 64 C F) =
                                      wordPathWork retCode (setVars values returned popped) :=
                                    wordPathWork_permStack_variant retCode
                                      (setVars values returned popped) k2 xs3 hrel3 hra hri
                                      (hretCode ▸ hca) (hretCode ▸ hci)
                                  exact wordPathWork_call_returning_result_variant values names retCode
                                    l1 l2 dest args handler s k xs vals0 args1 prog ss envs location
                                    returned s2 ({ s2 with permute := k2, stack := xs2 } :
                                      WordSemStateFiniteExact 64 C F) popped k2 xs3 hg hbad' hf hdom1
                                    hnodup hc hz hcv hpop hlocEq hlenEq hdu hrunT hpopT ihB ihRet
                                · rw [wordPathWork_call_returning_result_union_false values names
                                      retCode l1 l2 dest args handler s s2 popped vals0 envs args1 prog
                                      ss location returned hg hbad' hf hdom1 hnodup hc hz hfixS hpop
                                      hlocEq hlenEq hdu,
                                    wordPathWork_call_returning_result_union_false values names
                                      retCode l1 l2 dest args handler
                                      ({ s with permute := k, stack := xs } :
                                        WordSemStateFiniteExact 64 C F)
                                      ({ s2 with permute := k2, stack := xs2 } :
                                        WordSemStateFiniteExact 64 C F)
                                      ({ popped with permute := k2, stack := xs3 } :
                                        WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                      location returned (by rw [hgetT]; exact hg) hbad' hf hdom1
                                      hnodup hc hz hfixT hpopT hlocEq hlenEq (by simpa using hdu),
                                    ihB]
                        | exception location value =>
                            cases handler with
                            | none =>
                                rw [wordPathWork_call_returning_exception_unhandled values names
                                      retCode l1 l2 dest args none s s2 vals0 envs args1 prog ss
                                      location value hg hbad' hf hdom1 hnodup hc hz hfixS rfl,
                                    wordPathWork_call_returning_exception_unhandled values names
                                      retCode l1 l2 dest args none
                                      ({ s with permute := k, stack := xs } :
                                        WordSemStateFiniteExact 64 C F)
                                      ({ s2 with permute := k2, stack := xs2 } :
                                        WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                      location value (by rw [hgetT]; exact hg) hbad' hf hdom1 hnodup
                                      hc hz hfixT rfl, ihB]
                            | some hh =>
                                obtain ⟨reg, handlerCode, h1, h2⟩ := hh
                                have hha : noAllocSubprogsHOL handlerCode = true :=
                                  noAlloc_call_handler hna
                                have hhi : noInstallSubprogsHOL handlerCode = true :=
                                  noInstall_call_handler hni
                                by_cases hloc : location = .loc h1 h2
                                · by_cases hdu : sptDomainEqUnion s2.locals envs.1 envs.2
                                  · have hhandR : (setVar reg value s2).clock < s.clock := by
                                      have h1 : (setVar reg value s2).clock = s2.clock := rfl
                                      omega
                                    have hhandT : (setVar reg value s2).termdep = s.termdep := by
                                      have h1 : (setVar reg value s2).termdep = s2.termdep := rfl
                                      omega
                                    have hhandCode : (setVar reg value s2).code = s.code := by
                                      rw [show (setVar reg value s2).code = s2.code from rfl]
                                      exact hcode2
                                    have ihHand : wordPathWork handlerCode ({ setVar reg value s2 with
                                        permute := k2, stack := xs2 } :
                                          WordSemStateFiniteExact 64 C F) =
                                        wordPathWork handlerCode (setVar reg value s2) :=
                                      wordPathWork_permStack_variant handlerCode (setVar reg value s2)
                                        k2 xs2 hrel2 hha hhi (hhandCode ▸ hca) (hhandCode ▸ hci)
                                    exact wordPathWork_call_returning_exception_variant values names
                                      retCode l1 l2 dest args (some (reg, handlerCode, h1, h2)) s k xs vals0 args1 prog ss envs
                                      location value s2 k2 xs2 reg handlerCode h1 h2 hg hbad' hf
                                      hdom1 hnodup hc hz hcv rfl hloc hdu hrunT ihB ihHand
                                  · rw [wordPathWork_call_returning_exception_union_false values names
                                        retCode l1 l2 dest args (some (reg, handlerCode, h1, h2)) s s2 vals0 envs args1 prog ss
                                        location value reg handlerCode h1 h2 hg hbad' hf hdom1 hnodup
                                        hc hz hfixS rfl hloc hdu,
                                      wordPathWork_call_returning_exception_union_false values names
                                        retCode l1 l2 dest args (some (reg, handlerCode, h1, h2))
                                        ({ s with permute := k, stack := xs } :
                                          WordSemStateFiniteExact 64 C F)
                                        ({ s2 with permute := k2, stack := xs2 } :
                                          WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                        location value reg handlerCode h1 h2 (by rw [hgetT]; exact hg)
                                        hbad' hf hdom1 hnodup hc hz hfixT rfl hloc
                                        (by simpa using hdu), ihB]
                                · rw [wordPathWork_call_returning_exception_fall values names retCode
                                      l1 l2 dest args (some (reg, handlerCode, h1, h2)) s s2 vals0 envs args1 prog ss location
                                      value reg handlerCode h1 h2 hg hbad' hf hdom1 hnodup hc hz
                                      hfixS rfl hloc,
                                    wordPathWork_call_returning_exception_fall values names retCode
                                      l1 l2 dest args (some (reg, handlerCode, h1, h2))
                                      ({ s with permute := k, stack := xs } :
                                        WordSemStateFiniteExact 64 C F)
                                      ({ s2 with permute := k2, stack := xs2 } :
                                        WordSemStateFiniteExact 64 C F) vals0 envs args1 prog ss
                                      location value reg handlerCode h1 h2 (by rw [hgetT]; exact hg)
                                      hbad' hf hdom1 hnodup hc hz hfixT rfl hloc, ihB]
                        | «break» label =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs (some (.break label))
                                s2 ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                        | «continue» label =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs (some (.continue label))
                                s2 ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                        | timeOut =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs (some .timeOut) s2
                                ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                        | notEnoughSpace =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs
                                (some .notEnoughSpace) s2 ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                        | finalFfi ev =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs
                                (some (.finalFfi ev)) s2 ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]
                        | error =>
                            rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                                dest args handler s k xs vals0 args1 prog ss envs (some .error) s2
                                ({ s2 with permute := k2, stack := xs2 } :
                                  WordSemStateFiniteExact 64 C F) hg hbad' hf hdom1 hnodup hc hz hcv
                                (fun l r h => by cases h) (fun l v h => by cases h) hrunT ihB]

  termination_by p s k xs => (s.termdep, s.clock, sizeOf p)
  decreasing_by
    all_goals
      simp_wf
      apply wordSemLex
      try (have h1 := hdecR)
      try (have h2 := hdecT)
      try (have h3 := hdecR2)
      try (have h4 := hdecT2)
      try (have h5 := hretR)
      try (have h6 := hretT)
      try (have h7 := hhandR)
      try (have h8 := hhandT)
      try (have hfc := fixClock_IMP_LESS_EQ _ _ _ _ _h)
      try (have hcs := cutState_clock_termdep _ _ _ _hs)
      try (have hpc := popEnv_clock _ _ _hp)
      try (have hpt := popEnv_termdep _ _ _hp)
      try simp only [Flapjack.WordSemStateFiniteExact.callEnv,
        Flapjack.WordSemStateFiniteExact.decClock, Flapjack.WordSemStateFiniteExact.setVars,
        Flapjack.WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep,
        wordSemSTOP, true_and] at *
      omega
end InitECandidate.Runtime.FineCost
