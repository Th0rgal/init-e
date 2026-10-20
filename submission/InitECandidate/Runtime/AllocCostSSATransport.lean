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

end InitECandidate.Runtime.FineCost
