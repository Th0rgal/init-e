import InitECandidate.Runtime.WordPathWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax

/-!
# Cost invariance of `wordPathWork` under a value-equal stack swap

`wordPathWork` unfolds by structural recursion on the program and inspects the
state only through

* `locals` (`getVar`, `getVars`, `cutState`, `wordSemCutEnvs`),
* `code`, `stackSize` (the `wordSemFindCode` of a call),
* `clock`, `termdep`,
* the *frames pushed by the call itself* (via `pushEnv` from the cut
  environments) and the `popEnv` of those same frames at return.

The saved caller frames differ between the source and the renamed target only in
their environment keys, and they are never read: a returning callee exits before
the parent frame is popped, and the pop that rebuilds the caller's locals uses
the frame pushed by *this* call, which is built from the same cut environments
on both sides.  Hence the cost is invariant under replacing the stack by any
`WordSemStackEq.sValEq`-related stack (`stackSwapPost` is already stated in
terms of `sValEq`, so evaluation transports the result and non-stack fields).

This module collects the commuting lemmas for that proof; the main induction is
`wordPathWork_sValEq_stack_variant`.
-/

namespace InitECandidate.Runtime.WordToStack

open Flapjack Flapjack.WordSemStateFiniteExact

/-- `getVar` reads only the locals. -/
theorem getVar_stack {C F : Type} (name : Nat) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    getVar name { s with stack := xs } = getVar name s := rfl

/-- `getVars` reads only the locals. -/
theorem getVars_stack {C F : Type} :
    ∀ (args : List Nat) (s : WordSemStateFiniteExact 64 C F)
      (xs : List (WordSemStackFrame 64)),
      WordSemStateFiniteExact.getVars args { s with stack := xs } =
        WordSemStateFiniteExact.getVars args s
  | [], _, _ => rfl
  | _ :: vs, s, xs => by
      simp only [WordSemStateFiniteExact.getVars, getVar_stack, getVars_stack vs]

/-- `getVarImm` reads only the locals. -/
theorem getVarImm_stack {C F : Type} (operand : WordRegImm (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    getVarImm operand { s with stack := xs } = getVarImm operand s := by
  cases operand with
  | reg n => rfl
  | imm w => rfl

/-- Cutting a state touches only the locals, so it commutes with a stack swap. -/
theorem cutState_stack {C F : Type} (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    cutState names { s with stack := xs } =
      (match cutState names s with
        | none => none
        | some c => some { c with stack := xs }) := by
  unfold WordSemStateFiniteExact.cutState
  cases wordSemCutEnv names s.locals with
  | none => rfl
  | some env => rfl

/-- `decClock` touches only the clock. -/
theorem decClock_stack {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    decClock { s with stack := xs } = { decClock s with stack := xs } := rfl

/-- `setVar` touches only the locals. -/
theorem setVar_stack {C F : Type} (name : Nat) (value : WordLocW 64)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    setVar name value { s with stack := xs } = { setVar name value s with stack := xs } :=
  rfl

/-- `setVars` touches only the locals. -/
theorem setVars_stack {C F : Type} (names : List Nat) (values : List (WordLocW 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)) :
    setVars names values { s with stack := xs } =
      { setVars names values s with stack := xs } := rfl

/-- Pushing a cut frame commutes with a value-equal stack swap.  Wrapper over the
pinned `pushEnv_withStack` (the lemma the package's own `evaluateStackSwap_Call`
uses), in the `∃ ys, entry = {entry with stack := ys} ∧ sValEq` shape the cost
induction consumes. -/
theorem pushEnv_stack_swap {C F : Type}
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs) :
    ∃ ys, pushEnv envs handler { s with stack := xs } =
        { pushEnv envs handler s with stack := ys } ∧
      WordSemStackEq.sValEq (pushEnv envs handler s).stack ys := by
  obtain ⟨fr, hfr, hpe⟩ := WordSemStackEq.pushEnv_withStack envs handler s xs hval
  exact ⟨fr :: xs, hpe,
    by rw [hfr]; exact ⟨hval, of_eq_true (WordSemStackEq.sFrameValEqRefl fr)⟩⟩

/-- `callEnv` commutes with a value-equal stack swap (pinned
`callEnv_withStack`; only `stackMax` needs the equal stack sizes). -/
theorem callEnv_stack_swap {C F : Type} (args : List (WordLocW 64)) (size : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs) :
    ∃ ys, WordSemStateFiniteExact.callEnv args size { s with stack := xs } =
        { WordSemStateFiniteExact.callEnv args size s with stack := ys } ∧
      WordSemStackEq.sValEq (WordSemStateFiniteExact.callEnv args size s).stack ys :=
  ⟨xs, WordSemStackEq.callEnv_withStack args size s xs hval, hval⟩

#print axioms pushEnv_stack_swap
#print axioms callEnv_stack_swap


/-- `fixClock` preserves the stack. -/
theorem fixClock_stack_proj {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (r : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F) :
    (fixClock s r).2.stack = r.2.stack := rfl

/-- **Sequence case, normal completion.** -/
theorem wordPathWork_seq_sValEq_variant_none {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hev : evaluate first s = (none, middle))
    (ihFirst : wordPathWork first { s with stack := xs } = wordPathWork first s)
    (ihSecond : ∀ (m : WordSemStateFiniteExact 64 C F)
      (st : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq m.stack st →
      wordPathWork second { m with stack := st } = wordPathWork second m) :
    wordPathWork (.seq first second) { s with stack := xs } =
      wordPathWork (.seq first second) s := by
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap first s
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  dsimp only [WordSemStackEq.stackSwapRel] at hT
  obtain ⟨-, -, hrun⟩ := hT
  obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
  have hfix : fixClock { s with stack := xs }
      ((none : Option (WordSemResult 64)), { middle with stack := st }) =
      ((none : Option (WordSemResult 64)),
        { (fixClock s ((none : Option (WordSemResult 64)), middle)).2 with stack := st }) := by
    simp only [fixClock]
  have hL : wordPathWork (.seq first second) { s with stack := xs } =
      1 + wordPathWork first s +
        wordPathWork second
          { (fixClock s ((none : Option (WordSemResult 64)), middle)).2 with stack := st } := by
    rw [wordPathWork, hevT, ihFirst, hfix]
  have hR : wordPathWork (.seq first second) s =
      1 + wordPathWork first s +
        wordPathWork second (fixClock s ((none : Option (WordSemResult 64)), middle)).2 := by
    rw [wordPathWork, hev]
    simp [fixClock]
  have hst : WordSemStackEq.sValEq
      (fixClock s ((none : Option (WordSemResult 64)), middle)).2.stack st := by
    rw [fixClock_stack_proj]
    exact hvalT
  rw [hL, hR, ihSecond _ st hst]

/-- **Sequence case, exiting result.** -/
theorem wordPathWork_seq_sValEq_variant_result {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (s middle : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hev : evaluate first s = (some (.result location returned), middle))
    (ihFirst : wordPathWork first { s with stack := xs } = wordPathWork first s) :
    wordPathWork (.seq first second) { s with stack := xs } =
      wordPathWork (.seq first second) s := by
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap first s
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  dsimp only [WordSemStackEq.stackSwapRel] at hT
  obtain ⟨-, -, hrun⟩ := hT
  obtain ⟨st, hevT, -, -⟩ := hrun xs hval
  have hL : wordPathWork (.seq first second) { s with stack := xs } =
      1 + wordPathWork first s := by
    rw [wordPathWork, hevT, ihFirst]
    simp [fixClock]
  have hR : wordPathWork (.seq first second) s = 1 + wordPathWork first s := by
    rw [wordPathWork, hev]
    simp [fixClock]
  rw [hL, hR]


/-- **Conditional case.**  `getVar`/`getVarImm` read only the locals, so both
sides take the same branch and the two structural IHs close it. -/
theorem wordPathWork_ite_sValEq_variant {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (ih1 : wordPathWork first { s with stack := xs } = wordPathWork first s)
    (ih2 : wordPathWork second { s with stack := xs } = wordPathWork second s) :
    wordPathWork (.ite cmp reg operand first second) { s with stack := xs } =
      wordPathWork (.ite cmp reg operand first second) s := by
  rw [wordPathWork, wordPathWork, getVar_stack, getVarImm_stack]
  split <;> simp_all


/-- Unfolding the loop clause when the body completes normally, with the cut
state, body result and fixed middle state all named explicitly. -/
theorem wordPathWork_loop_unfold_of_none {C F : Type}
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (exitNames : WordLangNumSetHOL)
    (t c middle m : WordSemStateFiniteExact 64 C F)
    (htc : cutState (names, .ln) t = some c)
    (hev : evaluate body c = (none, middle))
    (hm : fixClock c (evaluate body c) = (none, m)) :
    wordPathWork (.loop names body exitNames) t =
      1 + wordPathWork body c +
        (if wordSemContLoop (none : Option (WordSemResult 64)) = true then
           (if m.clock = 0 then 0
            else wordPathWork (wordSemSTOP (.loop names body exitNames)) m.decClock)
         else 0) := by
  rw [wordPathWork]
  split
  · rename_i hnone
    rw [htc] at hnone
    cases hnone
  · rename_i cutSource hsome
    rw [htc] at hsome
    injection hsome with hcsEq
    subst hcsEq
    rw [hev] at hm ⊢
    split
    · rename_i r m0 hfix
      cases (hm.symm.trans hfix)
      dsimp only
      rfl

/-- **Loop case, body completes normally.** -/
theorem wordPathWork_loop_sValEq_variant_of_none {C F : Type}
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (exitNames : WordLangNumSetHOL)
    (s cs middle : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64))
    (hs : cutState (names, .ln) s = some cs)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hev : evaluate body cs = (none, middle))
    (ihBody : wordPathWork body { cs with stack := xs } = wordPathWork body cs)
    (ihStop : ∀ (m : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq m.stack st →
      wordPathWork (wordSemSTOP (.loop names body exitNames)) { m with stack := st } =
        wordPathWork (wordSemSTOP (.loop names body exitNames)) m) :
    wordPathWork (.loop names body exitNames) { s with stack := xs } =
      wordPathWork (.loop names body exitNames) s := by
  have hcsStack : cs.stack = s.stack := by
    unfold WordSemStateFiniteExact.cutState at hs
    cases hce : wordSemCutEnv (names, .ln) s.locals with
    | none => rw [hce] at hs; cases hs
    | some env => rw [hce] at hs; cases hs; rfl
  have hvalCs : WordSemStackEq.sValEq cs.stack xs := by rw [hcsStack]; exact hval
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap body cs
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  dsimp only [WordSemStackEq.stackSwapRel] at hT
  obtain ⟨-, -, hrun⟩ := hT
  obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hvalCs
  have hcs' : cutState (names, .ln) { s with stack := xs } = some { cs with stack := xs } := by
    rw [cutState_stack (names, .ln) s xs, hs]
  obtain ⟨m2, hm2⟩ : ∃ m, fixClock cs (evaluate body cs) = (none, m) :=
    ⟨_, by rw [hev]; rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m,
      fixClock { cs with stack := xs } (evaluate body { cs with stack := xs }) = (none, m) :=
    ⟨_, by rw [hevT]; rfl⟩
  have hm2' : fixClock cs ((none : Option (WordSemResult 64)), middle) = (none, m2) := by
    rw [← hm2, hev]
  have hm1' : fixClock { cs with stack := xs }
      ((none : Option (WordSemResult 64)), { middle with stack := st }) = (none, m1) := by
    rw [← hm1, hevT]
  have h2s : (fixClock cs ((none : Option (WordSemResult 64)), middle)).2 = m2 := by
    simpa using congrArg Prod.snd hm2'
  have hm2s : m2.stack = middle.stack := by
    rw [← h2s]
    exact fixClock_stack_proj cs ((none : Option (WordSemResult 64)), middle)
  have h1s : (fixClock { cs with stack := xs }
      ((none : Option (WordSemResult 64)), { middle with stack := st })).2 = m1 := by
    simpa using congrArg Prod.snd hm1'
  have hmRel : m1 = { m2 with stack := st } := by
    rw [← h1s, ← h2s]
    simp only [fixClock]
  rw [wordPathWork_loop_unfold_of_none names body exitNames s cs middle m2 hs hev hm2,
    wordPathWork_loop_unfold_of_none names body exitNames { s with stack := xs }
      { cs with stack := xs } { middle with stack := st } m1 hcs' hevT hm1, ihBody, hmRel]
  simp only [decClock_stack]
  rw [ihStop m2.decClock st (by
    show WordSemStackEq.sValEq m2.stack st
    rw [hm2s]
    exact hvalT)]

#print axioms wordPathWork_loop_sValEq_variant_of_none


/-- **Call entry shape (the pinned `hPx` core).**  Pushing the callee frame over a
value-equal stack yields the same frame `fr` on top, and the callee entry state
`callEnv args1 ss (pushEnv envs handler (decClock ·))` differs only in its stack
(`fr :: xs` versus `fr :: s.stack`).  This is the first ingredient of the `.call`
case, taken verbatim from `EvaluateStackSwap/Call.lean`'s `hPx`/`hvP`. -/
theorem callEntry_stack_swap {C F : Type}
    (args1 : List (WordLocW 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs) :
    ∃ fr, (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock s))).stack = fr :: s.stack ∧
      WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (decClock { s with stack := xs })) =
        { WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (decClock s)) with stack := fr :: xs } := by
  obtain ⟨fr, hfr, hpush⟩ :=
    WordSemStackEq.pushEnv_withStack envs handler
      (Flapjack.WordSemStateFiniteExact.decClock s) xs (by rw [decClock_stack]; exact hval)
  refine ⟨fr, ?_, ?_⟩
  · exact hfr
  · rw [decClock_stack, hpush]
    exact WordSemStackEq.callEnv_withStack args1 ss
      (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)) (fr :: xs) (by
        rw [hfr]
        exact ⟨hval, by simp [WordSemStackEq.sFrameValEqRefl]⟩)

#print axioms callEntry_stack_swap


/-- **Pop agreement over the same pushed frame (the Call return step).**  Two
states whose stacks have the *same* head frame pop to the same locals, the same
`localsSize`/`handler`, and tails `t` resp. `u`.  This is what makes the SSA
callee's `popEnv` agree with the source's: the frame popped is the one this very
call pushed (same `envs`), so no renamed ancestor frame is ever read. -/
theorem popEnv_stack_swap {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (fr : WordSemStackFrame 64) (t u : List (WordSemStackFrame 64)) :
    ∃ r, popEnv { s with stack := fr :: t } = some r ∧
      popEnv { s with stack := fr :: u } = some { r with stack := u } := by
  cases fr with
  | stackFrame m e0 e hh =>
    cases hh with
    | none => exact ⟨_, rfl, rfl⟩
    | some q =>
      obtain ⟨n, q1, q2⟩ := q
      exact ⟨_, rfl, rfl⟩

#print axioms popEnv_stack_swap



/-- `wordSemFindCode` reads only `code` and `stackSize`, so swapping the stack
leaves it unchanged (definitionally). -/
theorem wordSemFindCode_stack {C F : Type} (dest : Option Nat)
    (locs : List (WordLocW 64)) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    wordSemFindCode dest locs ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
        ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      wordSemFindCode dest locs s.code s.stackSize := rfl

/-- Unfolding the `.call` clause for a no-return tail call (`returns = none`,
`handler = none`) with the prelude results named: same `getVars`/`findCode`
success and a nonzero clock. -/
theorem wordPathWork_call_unfold_noreturn {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc
        (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
        locs) t.code t.stackSize = some (args1, prog, ss))
    (hnone : handler = none)
    (hclk : t.clock ≠ 0) :
    wordPathWork (.call none dest args handler) t =
      1 + wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (Flapjack.WordSemStateFiniteExact.decClock t)) := by
  subst hnone
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    subst hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      all_goals (try (rw [dif_neg hclk]))
      all_goals (try split)
      all_goals (try simp_all)
      all_goals (try rfl)

/-- **Call case, no-return tail call.** -/
theorem wordPathWork_call_noreturn_sValEq_variant {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args s = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc
        (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
        locs) s.code s.stackSize = some (args1, prog, ss))
    (hnone : handler = none)
    (hclk : s.clock ≠ 0)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (ihBody : wordPathWork prog
        { WordSemStateFiniteExact.callEnv args1 ss
            (Flapjack.WordSemStateFiniteExact.decClock s) with stack := xs } =
      wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (Flapjack.WordSemStateFiniteExact.decClock s))) :
    wordPathWork (.call none dest args handler) { s with stack := xs } =
      wordPathWork (.call none dest args handler) s := by
  have hgetL : WordSemStateFiniteExact.getVars args { s with stack := xs } = some locs := by
    rw [getVars_stack args s xs]; exact hget
  have hbadL : wordSemBadDestArgs dest args = false := hbad
  have hfindL : wordSemFindCode dest (wordSemAddRetLoc
      (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
      locs) ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize = some (args1, prog, ss) := by
    rw [wordSemFindCode_stack]
    exact hfind
  have hclkL : ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).clock ≠ 0 := hclk
  rw [wordPathWork_call_unfold_noreturn dest args handler prog args1 ss
      { s with stack := xs } locs hgetL hbadL hfindL hnone hclkL,
    wordPathWork_call_unfold_noreturn dest args handler prog args1 ss s locs hget hbad hfind hnone hclk]
  rw [decClock_stack,
    WordSemStackEq.callEnv_withStack args1 ss
      (Flapjack.WordSemStateFiniteExact.decClock s) xs
      (by rw [decClock_stack]; exact hval),
    ihBody]

#print axioms wordPathWork_call_noreturn_sValEq_variant


/-- A list of pairs is determined by its `fst`-image and its `snd`-image. -/
theorem map_fst_snd_eq {α β : Type} : ∀ (l l' : List (α × β)),
    l.map Prod.fst = l'.map Prod.fst → l.map Prod.snd = l'.map Prod.snd → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h1, _ => by simp at h1
  | _ :: _, [], h1, _ => by simp at h1
  | a :: as, b :: bs, h1, h2 => by
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      obtain ⟨h1a, h1t⟩ := h1
      obtain ⟨h2a, h2t⟩ := h2
      rw [Prod.ext h1a h2a, map_fst_snd_eq as bs h1t h2t]

#print axioms map_fst_snd_eq

#print axioms wordPathWork_ite_sValEq_variant

#print axioms wordPathWork_seq_sValEq_variant_none
#print axioms wordPathWork_seq_sValEq_variant_result


#print axioms getVar_stack
#print axioms getVars_stack
#print axioms getVarImm_stack
#print axioms cutState_stack
#print axioms decClock_stack
#print axioms setVar_stack
#print axioms setVars_stack


/-- A stack frame is determined by its key-equalities *and* value-equalities:
`sFrameValEq` pins the values and the length, `sFrameKeyEq` pins the keys, the
saved environment `e0` and the handler. -/
theorem frame_eq_of_valEq_keyEq (f g : WordSemStackFrame 64) :
    WordSemStackEq.sFrameValEq f g → WordSemStackEq.sFrameKeyEq f g → f = g := by
  cases f with
  | stackFrame n e0 ls hh =>
    cases g with
    | stackFrame n' e0' ls' hh' =>
      cases hh with
      | none =>
        cases hh' with
        | none =>
          intro h1 h2
          simp only [WordSemStackEq.sFrameValEq, WordSemStackEq.sFrameKeyEq] at h1 h2
          obtain ⟨hv, hn⟩ := h1
          obtain ⟨hk, he, _⟩ := h2
          cases hn
          cases he
          rw [map_fst_snd_eq ls ls' hk hv]
        | some y' =>
          intro h1
          simp only [WordSemStackEq.sFrameValEq] at h1
      | some y =>
        cases hh' with
        | none =>
          intro h1
          simp only [WordSemStackEq.sFrameValEq] at h1
        | some y' =>
          intro h1 h2
          simp only [WordSemStackEq.sFrameValEq, WordSemStackEq.sFrameKeyEq] at h1 h2
          obtain ⟨hv, hy, hn⟩ := h1
          obtain ⟨hk, _, he, _⟩ := h2
          cases hn
          cases he
          cases hy
          rw [map_fst_snd_eq ls ls' hk hv]

#print axioms frame_eq_of_valEq_keyEq

/-- `sFrameKeyEq` is symmetric. -/
theorem sFrameKeyEq_symm (a b : WordSemStackFrame 64) :
    WordSemStackEq.sFrameKeyEq a b → WordSemStackEq.sFrameKeyEq b a := by
  cases a with
  | stackFrame n e0 ls hh =>
    cases b with
    | stackFrame n' e0' ls' hh' =>
      cases hh <;> cases hh' <;>
        simp only [WordSemStackEq.sFrameKeyEq] <;> simp_all

/-- `sFrameKeyEq` is transitive. -/
theorem sFrameKeyEq_trans (a b c : WordSemStackFrame 64) :
    WordSemStackEq.sFrameKeyEq a b → WordSemStackEq.sFrameKeyEq b c →
      WordSemStackEq.sFrameKeyEq a c := by
  cases a with
  | stackFrame n e0 ls hh =>
    cases b with
    | stackFrame n' e0' ls' hh' =>
      cases c with
      | stackFrame n'' e0'' ls'' hh'' =>
        cases hh <;> cases hh' <;> cases hh'' <;>
          simp only [WordSemStackEq.sFrameKeyEq] <;> simp_all

/-- **Pop agreement for the returning call.**  If the two stacks have the same
head *keys* (both key-equal to the frame `fr` this call pushed) and are
value-equal, then their head frames are literally equal and `popEnv` yields the
same locals, with the tails `rest` resp. `u`. -/
theorem popEnv_agree {C F : Type} (middle : WordSemStateFiniteExact 64 C F)
    (st : List (WordSemStackFrame 64)) (fr fM fS : WordSemStackFrame 64)
    (rest u : List (WordSemStackFrame 64))
    (hms : middle.stack = fM :: rest) (hst : st = fS :: u)
    (hM : WordSemStackEq.sFrameKeyEq fr fM)
    (hS : WordSemStackEq.sFrameKeyEq fr fS)
    (hval : WordSemStackEq.sValEq middle.stack st) :
    ∃ popped, popEnv middle = some popped ∧
      popEnv { middle with stack := st } = some { popped with stack := u } := by
  have hval' : WordSemStackEq.sValEq (fM :: rest) (fS :: u) := by
    rw [← hms, ← hst]; exact hval
  have hfv : WordSemStackEq.sFrameValEq fM fS := hval'.2
  have hfk : WordSemStackEq.sFrameKeyEq fM fS :=
    sFrameKeyEq_trans fM fr fS (sFrameKeyEq_symm fr fM hM) hS
  have hfeq : fM = fS := frame_eq_of_valEq_keyEq fM fS hfv hfk
  rw [← hfeq] at hst
  have hm' : ({ middle with stack := fM :: rest } : WordSemStateFiniteExact 64 C F) = middle := by
    rw [← hms]
  obtain ⟨r, hr1, hr2⟩ := popEnv_stack_swap middle fM rest u
  refine ⟨r, ?_, ?_⟩
  · rw [← hm']
    exact hr1
  · rw [hst]
    exact hr2

#print axioms popEnv_agree

/-- Unfolding the `.call` clause for a **returning** call with the prelude results
named and the taken branches supplied. -/
theorem wordPathWork_call_unfold_result {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle popped : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.result location returned), middle))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = some popped)
    (hdom : sptDomainEqUnion popped.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) +
        wordPathWork retCode (WordSemStateFiniteExact.setVars values returned popped) := by
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          dsimp only
          split
          all_goals (try simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.result.injEq,
            WordSemResult.exception.injEq] at *)
          all_goals (try rw [if_neg hnl])
          all_goals (try rw [hpop])
          all_goals (try rw [if_pos hdom])
          all_goals (try dsimp only [])
          all_goals (try rfl)
          all_goals simp_all

#print axioms wordPathWork_call_unfold_result

/-- **Call case, exiting result** (transport). -/
theorem wordPathWork_call_result_sValEq_variant {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (locs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle middleT : WordSemStateFiniteExact 64 C F)
    (popped : WordSemStateFiniteExact 64 C F) (u : List (WordSemStackFrame 64))
    (hget : WordSemStateFiniteExact.getVars args s = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        s.code s.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hclk : s.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
        = (some (.result location returned), middle))
    (hfixT : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs })))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))))
        = (some (.result location returned), middleT))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = some popped)
    (hpopT : popEnv middleT = some { popped with stack := u })
    (hdom : sptDomainEqUnion popped.locals envs.1 envs.2)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hvalPop : WordSemStackEq.sValEq popped.stack u)
    (ihBodyAt : wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))) =
      wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
    (ihRet : ∀ (m : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq m.stack st →
      wordPathWork retCode { m with stack := st } = wordPathWork retCode m) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
        { s with stack := xs } =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetL : WordSemStateFiniteExact.getVars args { s with stack := xs } = some locs := by
    rw [getVars_stack args s xs]; exact hget
  have hfindL : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize = some (args1, prog, ss) := by
    rw [wordSemFindCode_stack]
    exact hfind
  rw [wordPathWork_call_unfold_result (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (prog := prog) (args1 := args1) (ss := ss) (t := { s with stack := xs }) (locs := locs)
      (envs := envs) (location := location) (returned := returned) (middle := middleT)
      (popped := { popped with stack := u }) (hget := hgetL) (hbad := hbad) (hfind := hfindL)
      (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfixT) (hnl := hnl) (hpop := hpopT)
      (hdom := hdom),
    wordPathWork_call_unfold_result (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (prog := prog) (args1 := args1) (ss := ss) (t := s) (locs := locs)
      (envs := envs) (location := location) (returned := returned) (middle := middle)
      (popped := popped) (hget := hget) (hbad := hbad) (hfind := hfind) (hnd := hnd)
      (hcut := hcut) (hclk := hclk) (hfix := hfix) (hnl := hnl) (hpop := hpop)
      (hdom := hdom)]
  rw [ihBodyAt, setVars_stack, ihRet (WordSemStateFiniteExact.setVars values returned popped) u hvalPop]

#print axioms wordPathWork_call_result_sValEq_variant

/-- Unfolding the `.call` clause for a call that exits with an **exception**. -/
theorem wordPathWork_call_unfold_exception {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.exception location value), middle))
    (hhand : handler = some (reg, handlerCode, h1, h2))
    (hloc : location = .loc h1 h2)
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) +
        wordPathWork handlerCode (WordSemStateFiniteExact.setVar reg value middle) := by
  rw [wordPathWork]
  split
  · rename_i h1'
    rw [hget] at h1'
    cases h1'
  · rename_i locs1 h1'
    rw [hget] at h1'
    injection h1' with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2'
      rw [hfind] at h2'
      cases h2'
    · rename_i a1 p1 ss1 h2'
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2'
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          dsimp only
          split
          all_goals (try simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.result.injEq,
            WordSemResult.exception.injEq] at *)
          all_goals (try rw [hhand])
          all_goals (try split)
          all_goals (try simp only [Prod.mk.injEq, Option.some.injEq] at *)
          all_goals (try rw [if_neg hloc])
          all_goals (try rw [if_pos hdom])
          all_goals (try dsimp only [])
          all_goals (try rfl)
          all_goals simp_all

#print axioms wordPathWork_call_unfold_exception

/-- `setVar` leaves the stack alone. -/
theorem setVar_stack_proj {C F : Type} (name : Nat) (value : WordLocW 64)
    (s : WordSemStateFiniteExact 64 C F) :
    (WordSemStateFiniteExact.setVar name value s).stack = s.stack := by
  have h := setVar_stack (C := C) (F := F) name value s s.stack
  simpa using congrArg (fun x => x.stack) h

/-- **Call case, exiting exception** (transport). -/
theorem wordPathWork_call_exception_sValEq_variant {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (locs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (value : WordLocW 64)
    (middle middleT : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64))
    (hget : WordSemStateFiniteExact.getVars args s = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        s.code s.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hclk : s.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
        = (some (.exception location value), middle))
    (hfixT : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs })))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))))
        = (some (.exception location value), middleT))
    (hhand : handler = some (reg, handlerCode, h1, h2))
    (hloc : location = .loc h1 h2)
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (hdomT : sptDomainEqUnion middleT.locals envs.1 envs.2)
    (hmidT : middleT = { middle with stack := st })
    (hvalMid : WordSemStackEq.sValEq middle.stack st)
    (ihBodyAt : wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))) =
      wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
    (ihHand : ∀ (m : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq m.stack st →
      wordPathWork handlerCode { m with stack := st } = wordPathWork handlerCode m) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
        { s with stack := xs } =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetL : WordSemStateFiniteExact.getVars args { s with stack := xs } = some locs := by
    rw [getVars_stack args s xs]; exact hget
  have hfindL : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize = some (args1, prog, ss) := by
    rw [wordSemFindCode_stack]
    exact hfind
  rw [wordPathWork_call_unfold_exception (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (reg := reg) (handlerCode := handlerCode) (h1 := h1) (h2 := h2) (prog := prog)
      (args1 := args1) (ss := ss) (t := { s with stack := xs }) (locs := locs) (envs := envs)
      (location := location) (value := value) (middle := middleT) (hget := hgetL) (hbad := hbad)
      (hfind := hfindL) (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfixT) (hhand := hhand)
      (hloc := hloc) (hdom := hdomT),
    wordPathWork_call_unfold_exception (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (reg := reg) (handlerCode := handlerCode) (h1 := h1) (h2 := h2) (prog := prog)
      (args1 := args1) (ss := ss) (t := s) (locs := locs) (envs := envs)
      (location := location) (value := value) (middle := middle) (hget := hget) (hbad := hbad)
      (hfind := hfind) (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfix) (hhand := hhand)
      (hloc := hloc) (hdom := hdom)]
  rw [ihBodyAt, hmidT, setVar_stack,
    ihHand (WordSemStateFiniteExact.setVar reg value middle) st (by
      rw [setVar_stack_proj]
      exact hvalMid)]

#print axioms wordPathWork_call_exception_sValEq_variant

/-- `fixClock` on a stack-swapped state: the result is the same, and the state's
stack is the swapped one (the rest of the record comes from `s`/`m`, unchanged). -/
theorem fixClock_stack_swap {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) (r : Option (WordSemResult 64))
    (m : WordSemStateFiniteExact 64 C F) :
    fixClock { s with stack := xs } (r, { m with stack := xs }) =
      (r, { (fixClock s (r, m)).2 with stack := xs }) := by
  cases r <;> (simp only [fixClock]; try rfl)

#print axioms fixClock_stack_swap

#print Flapjack.wordSemLastN

/-- The locals restored by an exception frame are determined by the frame's saved
environment and by the key- and value-images of the popped environment list.
This is the algebraic core of the exception-domain argument: on both runs the
frame that `wordSemLastN` selects is the *same* pushed frame (its handler index
is the pre-push stack length, and the two stacks have equal length), so `e0` and
`e` agree, and `lss`/`lss'` agree in keys (`map fst e = map fst lss`) and in
values (`stackSwapPost`). -/
theorem sptUnion_env_eq (e0 e0' : List (Nat × WordLocW 64))
    (lss lss' : List (Nat × WordLocW 64))
    (he0 : e0 = e0')
    (hfst : List.map Prod.fst lss = List.map Prod.fst lss')
    (hsnd : List.map Prod.snd lss = List.map Prod.snd lss') :
    Flapjack.sptUnion (Flapjack.sptFromAList lss) (Flapjack.sptFromAList e0) =
      Flapjack.sptUnion (Flapjack.sptFromAList lss') (Flapjack.sptFromAList e0') := by
  rw [map_fst_snd_eq lss lss' hfst hsnd, he0]

#print axioms sptUnion_env_eq

/-- `wordSemLastN` selects the whole stack when asked for `length + 1` frames;
in particular the frame pushed by the call is the *same* term in both runs. -/
theorem wordSemLastN_length_succ_cons {α : Type} (fr : α) (rest : List α) :
    Flapjack.wordSemLastN (rest.length + 1) (fr :: rest) = fr :: rest := by
  simp only [Flapjack.wordSemLastN, List.reverse_cons, List.length_append, List.length_cons,
    List.length_nil]
  rw [List.take_of_length_le (by simp)]
  simp

#print axioms wordSemLastN_length_succ_cons

/-! ### Prelude lemmas for the `.call` clause

Each one pins `wordPathWork` of a call to `1` when one of the clause's guards
fails.  These are the "cheap" branches of the guarded driver. -/
theorem wordPathWork_call_getVars_none {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = none) :
    wordPathWork (.call ret dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h

theorem wordPathWork_call_badDest {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = true) :
    wordPathWork (.call ret dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_pos hbad]

theorem wordPathWork_call_findCode_none {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc ret locs) t.code t.stackSize = none) :
    wordPathWork (.call ret dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf

theorem wordPathWork_call_returning_dom {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hdc : sptDomainEmpty names.1 ∨ ¬ values.Nodup) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf
      split
      · rename_i hc
        simp at hc
      · rename_i v1 n1 rc1 m1 q1 hc
        cases hc
        rw [if_pos hdc]

theorem wordPathWork_call_returning_cut_none {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hce : wordSemCutEnvs names t.locals = none) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf
      split
      · rename_i hc
        simp at hc
      · rename_i v1 n1 rc1 m1 q1 hc
        cases hc
        rw [if_neg hnd]
        split
        · rfl
        · rename_i envs1 hcu
          rw [hce] at hcu
          cases hcu

theorem wordPathWork_call_none_clock_zero {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hhand : handler = none) (hz : t.clock = 0) :
    wordPathWork (.call none dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf
      subst hhand
      rw [dif_pos hz]

theorem wordPathWork_call_returning_clock_zero {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hce : wordSemCutEnvs names t.locals = some envs) (hz : t.clock = 0) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf
      split
      · rename_i hc
        simp at hc
      · rename_i v1 n1 rc1 m1 q1 hc
        cases hc
        rw [if_neg hnd]
        split
        · rfl
        · rename_i envs1 hcu
          rw [hce] at hcu
          cases hcu
          rw [dif_pos hz]

/-- `fixClock` on a stack-swapped state, with *independent* stacks for the
result state and for the clock source: it only reads `clock`/`termdep` from `s`
and the result state's non-stack fields from `m`. -/
theorem fixClock_swap_stack {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) (r : Option (WordSemResult 64))
    (m : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64)) :
    fixClock { s with stack := xs } (r, { m with stack := st }) =
      (r, { (fixClock s (r, m)).2 with stack := st }) := by
  cases r <;> (simp only [fixClock]; try rfl)

#print axioms fixClock_swap_stack


/-- `wordSemLastN` at the full length returns the whole stack. -/
theorem wordSemLastN_length {α : Type} (l : List α) : Flapjack.wordSemLastN l.length l = l := by
  simp only [Flapjack.wordSemLastN]
  rw [List.take_of_length_le (by simp)]
  simp

/-- Prelude: a tail call with a handler contributes `1`. -/
theorem wordPathWork_call_none_handler {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hhand : ∃ x, handler = some x) :
    wordPathWork (.call none dest args handler) t = 1 := by
  rw [wordPathWork]
  split
  · rfl
  · rename_i locs1 h
    rw [hget] at h
    cases h
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rfl
    · rename_i a1 p1 ss1 hf
      rw [hfind] at hf
      cases hf
      obtain ⟨x, rfl⟩ := hhand
      split
      · rfl
      · rename_i hc
        simp at hc

#print axioms wordSemLastN_length
#print axioms wordPathWork_call_none_handler

/-! ### Fall-through `.call` tails: the post-processing contributes `0` -/

theorem wordPathWork_call_result_mismatch {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.result location returned), middle))
    (hnl : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try (simp only [if_pos hnl]))
          all_goals (try omega)

theorem wordPathWork_call_result_pop_none {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.result location returned), middle))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = none) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try (simp only [if_neg hnl]))
          all_goals (try (rw [hpop]))
          all_goals (try omega)

theorem wordPathWork_call_result_dom_false {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle popped : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.result location returned), middle))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = some popped)
    (hdom : ¬ sptDomainEqUnion popped.locals envs.1 envs.2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try (simp only [if_neg hnl]))
          all_goals (try (rw [hpop]))
          all_goals (try (simp only [if_neg hdom]))
          all_goals (try omega)

theorem wordPathWork_call_other_result {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (res : Option (WordSemResult 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (res, middle))
    (h1 : ∀ (location : WordLocW 64) (returned : List (WordLocW 64)),
        res ≠ some (.result location returned))
    (h2 : ∀ (location : WordLocW 64) (value : WordLocW 64),
        res ≠ some (.exception location value)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1
    rw [hget] at h1
    cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2
      rw [hfind] at h2
      cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try omega)

theorem wordPathWork_call_exception_none_handler {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.exception location value), middle))
    (hhand : handler = none) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1'
    rw [hget] at h1'
    cases h1'
  · rename_i locs1 h1'
    rw [hget] at h1'
    injection h1' with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2'
      rw [hfind] at h2'
      cases h2'
    · rename_i a1 p1 ss1 h2'
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2'
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try (rw [hhand]))
          all_goals (try omega)

theorem wordPathWork_call_exception_loc_mismatch {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (location : WordLocW 64) (value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.exception location value), middle))
    (hhand : handler = some (reg, handlerCode, h1, h2))
    (hloc : location ≠ .loc h1 h2) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) t =
      1 + wordPathWork prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))) := by
  rw [wordPathWork]
  split
  · rename_i h1'
    rw [hget] at h1'
    cases h1'
  · rename_i locs1 h1'
    rw [hget] at h1'
    injection h1' with hx
    cases hx
    rw [if_neg (by rw [hbad]; simp)]
    split
    · rename_i h2'
      rw [hfind] at h2'
      cases h2'
    · rename_i a1 p1 ss1 h2'
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2'
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        split
        · rename_i h3
          rw [hcut] at h3
          cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          all_goals (try simp_all)
          all_goals (try (rw [hhand]))
          all_goals (try (simp only [if_pos hloc]))
          all_goals (try omega)

/-! ### Error propagation from a non-erroring parent

`WordSemResult.error` is never caught (`handler`s catch `exception` only), so a
non-erroring program has non-erroring reached children.  These lemmas discharge
the `stackSwapPost` non-error side conditions on *reached* paths only. -/

theorem evaluate_seq_error_fst {C F : Type} (c1 c2 : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F)
    (h : (evaluate c1 s).1 = some (WordSemResult.error)) :
    (evaluate (.seq c1 c2) s).1 = some (WordSemResult.error) := by
  rw [evaluate]
  split
  · rename_i res s1 hfix
    have hfst : res = (evaluate c1 s).1 := (congrArg Prod.fst hfix).symm
    rw [hfst, h]

theorem evaluate_seq_error_snd {C F : Type} (c1 c2 : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F)
    (h1 : (evaluate c1 s).1 = none)
    (h2 : (evaluate c2 (fixClock s (evaluate c1 s)).2).1 = some (WordSemResult.error)) :
    (evaluate (.seq c1 c2) s).1 = some (WordSemResult.error) := by
  rw [evaluate]
  split
  · rename_i res s1 hfix
    have hfst : res = (evaluate c1 s).1 := (congrArg Prod.fst hfix).symm
    have hsnd : s1 = (fixClock s (evaluate c1 s)).2 := (congrArg Prod.snd hfix).symm
    rw [hfst, h1, hsnd]
    exact h2

theorem evaluate_ite_error_true {C F : Type} (cmp : Cmp) (reg : Nat)
    (operand : WordRegImm (BitVec 64)) (c1 c2 : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (x y : WordLocW 64)
    (hv : WordSemStateFiniteExact.getVar reg s = some x)
    (hi : WordSemStateFiniteExact.getVarImm operand s = some y)
    (hc : wordSemWordCmp cmp x y = some true)
    (h : (evaluate c1 s).1 = some (WordSemResult.error)) :
    (evaluate (.ite cmp reg operand c1 c2) s).1 = some (WordSemResult.error) := by
  simp only [evaluate, hv, hi, hc]
  exact h

theorem evaluate_ite_error_false {C F : Type} (cmp : Cmp) (reg : Nat)
    (operand : WordRegImm (BitVec 64)) (c1 c2 : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (x y : WordLocW 64)
    (hv : WordSemStateFiniteExact.getVar reg s = some x)
    (hi : WordSemStateFiniteExact.getVarImm operand s = some y)
    (hc : wordSemWordCmp cmp x y = some false)
    (h : (evaluate c2 s).1 = some (WordSemResult.error)) :
    (evaluate (.ite cmp reg operand c1 c2) s).1 = some (WordSemResult.error) := by
  simp only [evaluate, hv, hi, hc]
  exact h

theorem evaluate_loop_error_body {C F : Type} (names : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (s cs : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cs)
    (h : (evaluate body cs).1 = some (WordSemResult.error)) :
    (evaluate (.loop names body exitNames) s).1 = some (WordSemResult.error) := by
  rw [evaluate, hs]
  split
  · rfl
  · rename_i s' hs'
    injection hs' with hx
    cases hx
    split
    · rename_i res s1 hfix
      have hfst : res = (evaluate body cs).1 := (congrArg Prod.fst hfix).symm
      rw [hfst, h]
      rfl

theorem evaluate_loop_error_stop {C F : Type} (names : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (s cs : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cs)
    (res : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F)
    (hfix : fixClock cs (evaluate body cs) = (res, s1))
    (hc : wordSemContLoop res = true) (hz : ¬ s1.clock = 0)
    (h : (evaluate (wordSemSTOP (.loop names body exitNames)) (Flapjack.WordSemStateFiniteExact.decClock s1)).1
        = some (WordSemResult.error)) :
    (evaluate (.loop names body exitNames) s).1 = some (WordSemResult.error) := by
  rw [evaluate, hs]
  split
  · rfl
  · rename_i s' hs'
    injection hs' with hx
    cases hx
    split
    · rename_i res' s1' hfix'
      rw [hfix] at hfix'
      cases hfix'
      rw [hc]
      rw [dif_neg hz]
      exact h

theorem evaluate_call_error_body {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (WordSemResult.error), middle)) :
    (evaluate (.call (some (values, names, retCode, l1, l2)) dest args handler) t).1 =
      some (WordSemResult.error) := by
  rw [evaluate]
  try split
  · rename_i h1
    rw [hget] at h1
    try cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    try cases hx
    rw [if_neg (by rw [hbad]; simp)]
    try split
    · rename_i h2
      rw [hfind] at h2
      try cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      try split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        try split
        · rename_i h3
          rw [hcut] at h3
          try cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          try cases hx3
          rw [dif_neg hclk]
          rw [hfix]

theorem evaluate_call_error_ret {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle popped : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.result location returned), middle))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = some popped)
    (hdom : sptDomainEqUnion popped.locals envs.1 envs.2)
    (h : (evaluate retCode (WordSemStateFiniteExact.setVars values returned popped)).1
      = some (WordSemResult.error)) :
    (evaluate (.call (some (values, names, retCode, l1, l2)) dest args handler) t).1 =
      some (WordSemResult.error) := by
  rw [evaluate]
  try split
  · rename_i h1
    rw [hget] at h1
    try cases h1
  · rename_i locs1 h1
    rw [hget] at h1
    injection h1 with hx
    try cases hx
    rw [if_neg (by rw [hbad]; simp)]
    try split
    · rename_i h2
      rw [hfind] at h2
      try cases h2
    · rename_i a1 p1 ss1 h2
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      try split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        try split
        · rename_i h3
          rw [hcut] at h3
          try cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          try cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          try dsimp only
          try split
          all_goals (try simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.result.injEq,
            WordSemResult.exception.injEq] at *)
          all_goals (try rw [if_neg hnl])
          all_goals (try rw [hpop])
          all_goals (try rw [if_pos hdom])
          all_goals (try dsimp only [])
          all_goals (try exact h)
          all_goals simp_all

theorem evaluate_call_error_handler {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (t : WordSemStateFiniteExact 64 C F) (locs : List (WordLocW 64))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (location value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hget : WordSemStateFiniteExact.getVars args t = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        t.code t.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names t.locals = some envs)
    (hclk : t.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock t))))
        = (some (.exception location value), middle))
    (hhand : handler = some (reg, handlerCode, h1, h2))
    (hloc : location = .loc h1 h2)
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (h : (evaluate handlerCode (WordSemStateFiniteExact.setVar reg value middle)).1
      = some (WordSemResult.error)) :
    (evaluate (.call (some (values, names, retCode, l1, l2)) dest args handler) t).1 =
      some (WordSemResult.error) := by
  rw [evaluate]
  try split
  · rename_i h1'
    rw [hget] at h1'
    try cases h1'
  · rename_i locs1 h1'
    rw [hget] at h1'
    injection h1' with hx
    try cases hx
    rw [if_neg (by rw [hbad]; simp)]
    try split
    · rename_i h2'
      rw [hfind] at h2'
      try cases h2'
    · rename_i a1 p1 ss1 h2'
      have hinj : some (args1, prog, ss) = some (a1, p1, ss1) := hfind.symm.trans h2'
      simp only [Option.some.injEq, Prod.mk.injEq] at hinj
      obtain ⟨rfl, rfl, rfl⟩ := hinj
      try split
      · rename_i hsome
        simp at hsome
      · rename_i v1 n1 rc1 m1 q1 hsome
        have hinj2 : some (values, names, retCode, l1, l2) = some (v1, n1, rc1, m1, q1) := hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hinj2
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hinj2
        rw [if_neg hnd]
        try split
        · rename_i h3
          rw [hcut] at h3
          try cases h3
        · rename_i envs1 h3
          rw [hcut] at h3
          injection h3 with hx3
          try cases hx3
          rw [dif_neg hclk]
          rw [hfix]
          try dsimp only
          try split
          all_goals (try simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.result.injEq,
            WordSemResult.exception.injEq] at *)
          all_goals (try rw [hhand])
          all_goals (try rw [if_pos hloc])
          all_goals (try rw [if_pos hdom])
          all_goals (try dsimp only [])
          all_goals (try exact h)
          all_goals simp_all

/-! ### Pointwise-IH variants of the case lemmas

The driver carries the top-level non-error hypothesis only, so the recursive
hypotheses are needed at the *specific* reached states (not uniformly). -/

theorem wordPathWork_call_result_at {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (locs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle middleT : WordSemStateFiniteExact 64 C F)
    (popped : WordSemStateFiniteExact 64 C F) (u : List (WordSemStackFrame 64))
    (hget : WordSemStateFiniteExact.getVars args s = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        s.code s.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hclk : s.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
        = (some (.result location returned), middle))
    (hfixT : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs })))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))))
        = (some (.result location returned), middleT))
    (hnl : ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length))
    (hpop : popEnv middle = some popped)
    (hpopT : popEnv middleT = some { popped with stack := u })
    (hdom : sptDomainEqUnion popped.locals envs.1 envs.2)
    (ihBodyAt : wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))) =
      wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
    (ihRetAt : wordPathWork retCode
        { WordSemStateFiniteExact.setVars values returned popped with stack := u } =
      wordPathWork retCode (WordSemStateFiniteExact.setVars values returned popped)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
        { s with stack := xs } =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetL : WordSemStateFiniteExact.getVars args { s with stack := xs } = some locs := by
    rw [getVars_stack args s xs]; exact hget
  have hfindL : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize = some (args1, prog, ss) := by
    rw [wordSemFindCode_stack]
    exact hfind
  rw [wordPathWork_call_unfold_result (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (prog := prog) (args1 := args1) (ss := ss) (t := { s with stack := xs }) (locs := locs)
      (envs := envs) (location := location) (returned := returned) (middle := middleT)
      (popped := { popped with stack := u }) (hget := hgetL) (hbad := hbad) (hfind := hfindL)
      (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfixT) (hnl := hnl) (hpop := hpopT)
      (hdom := hdom),
    wordPathWork_call_unfold_result (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (prog := prog) (args1 := args1) (ss := ss) (t := s) (locs := locs)
      (envs := envs) (location := location) (returned := returned) (middle := middle)
      (popped := popped) (hget := hget) (hbad := hbad) (hfind := hfind) (hnd := hnd)
      (hcut := hcut) (hclk := hclk) (hfix := hfix) (hnl := hnl) (hpop := hpop)
      (hdom := hdom)]
  rw [ihBodyAt, setVars_stack, ihRetAt]

theorem wordPathWork_call_exception_at {C F : Type}
    (dest : Option Nat) (args : List Nat) (values : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (reg : Nat) (handlerCode : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (args1 : List (WordLocW 64)) (ss : Option Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (locs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (value : WordLocW 64)
    (middle middleT : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64))
    (hget : WordSemStateFiniteExact.getVars args s = some locs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest
        (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
        s.code s.stackSize = some (args1, prog, ss))
    (hnd : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (hcut : wordSemCutEnvs names s.locals = some envs)
    (hclk : s.clock ≠ 0)
    (hfix : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s)))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
        = (some (.exception location value), middle))
    (hfixT : fixClock
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs })))
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))))
        = (some (.exception location value), middleT))
    (hhand : handler = some (reg, handlerCode, h1, h2))
    (hloc : location = .loc h1 h2)
    (hmidT : middleT = { middle with stack := st })
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (hdomT : sptDomainEqUnion middleT.locals envs.1 envs.2)
    (ihBodyAt : wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock { s with stack := xs }))) =
      wordPathWork prog
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv envs handler (Flapjack.WordSemStateFiniteExact.decClock s))))
    (ihHandAt : wordPathWork handlerCode
        { WordSemStateFiniteExact.setVar reg value middle with stack := st } =
      wordPathWork handlerCode (WordSemStateFiniteExact.setVar reg value middle)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
        { s with stack := xs } =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetL : WordSemStateFiniteExact.getVars args { s with stack := xs } = some locs := by
    rw [getVars_stack args s xs]; exact hget
  have hfindL : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) locs)
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with stack := xs } : WordSemStateFiniteExact 64 C F).stackSize = some (args1, prog, ss) := by
    rw [wordSemFindCode_stack]
    exact hfind
  rw [wordPathWork_call_unfold_exception (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (reg := reg) (handlerCode := handlerCode) (h1 := h1) (h2 := h2) (prog := prog)
      (args1 := args1) (ss := ss) (t := { s with stack := xs }) (locs := locs) (envs := envs)
      (location := location) (value := value) (middle := middleT) (hget := hgetL) (hbad := hbad)
      (hfind := hfindL) (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfixT) (hhand := hhand)
      (hloc := hloc) (hdom := hdomT),
    wordPathWork_call_unfold_exception (dest := dest) (args := args) (values := values)
      (names := names) (retCode := retCode) (l1 := l1) (l2 := l2) (handler := handler)
      (reg := reg) (handlerCode := handlerCode) (h1 := h1) (h2 := h2) (prog := prog)
      (args1 := args1) (ss := ss) (t := s) (locs := locs) (envs := envs) (location := location)
      (value := value) (middle := middle) (hget := hget) (hbad := hbad) (hfind := hfind)
      (hnd := hnd) (hcut := hcut) (hclk := hclk) (hfix := hfix) (hhand := hhand) (hloc := hloc)
      (hdom := hdom)]
  rw [ihBodyAt, hmidT, setVar_stack, ihHandAt]

/-! ### Driver support lemmas

`fixClock` projections, `cutState` stack projection in constructor form, and the
`spt` domain key interface used to identify the exception-restored locals
domains of the two runs. -/

theorem fixClock_fst {C F β : Type} (s : WordSemStateFiniteExact 64 C F)
    (p : β × WordSemStateFiniteExact 64 C F) : (fixClock s p).1 = p.1 := rfl

theorem fixClock_snd_stack {C F β : Type} (s : WordSemStateFiniteExact 64 C F)
    (p : β × WordSemStateFiniteExact 64 C F) : (fixClock s p).2.stack = p.2.stack := rfl

theorem fixClock_snd_locals {C F β : Type} (s : WordSemStateFiniteExact 64 C F)
    (p : β × WordSemStateFiniteExact 64 C F) : (fixClock s p).2.locals = p.2.locals := rfl

theorem cutState_stack_none {C F : Type} (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hs : cutState names s = none) : cutState names { s with stack := xs } = none := by
  rw [cutState_stack names s xs, hs]

theorem cutState_stack_some {C F : Type} (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (cs : WordSemStateFiniteExact 64 C F) (hs : cutState names s = some cs) :
    cutState names { s with stack := xs } = some { cs with stack := xs } := by
  rw [cutState_stack names s xs, hs]

theorem sptMem_sptFromAList {α : Type} (k : Nat) (xs : List (Nat × α)) :
    sptMem k (sptFromAList xs) ↔ k ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [sptFromAList, sptMem, sptDomain, sptLookup]
  | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      simp only [sptFromAList, List.map_cons, List.mem_cons]
      rw [sptMem_sptInsert, ih]

theorem sptDomainEqUnion_congr {α β γ : Type} {lss lss' e0 e0' : List (Nat × α)}
    {b : Spt β} {c : Spt γ}
    (h1 : lss.map Prod.fst = lss'.map Prod.fst)
    (h2 : e0.map Prod.fst = e0'.map Prod.fst)
    (h : sptDomainEqUnion (sptUnion (sptFromAList lss) (sptFromAList e0)) b c) :
    sptDomainEqUnion (sptUnion (sptFromAList lss') (sptFromAList e0')) b c := by
  intro k
  have h' := h k
  simp only [sptMem_sptUnion, sptMem_sptFromAList, h1, h2] at h' ⊢
  exact h'

theorem sFrameValEq_refl (fr : WordSemStackFrame 64) :
    WordSemStackEq.sFrameValEq fr fr := by
  obtain ⟨m, l0, l, y⟩ := fr
  cases y <;> simp [WordSemStackEq.sFrameValEq]

theorem sValEq_cons_self (fr : WordSemStackFrame 64)
    {as bs : List (WordSemStackFrame 64)}
    (h : WordSemStackEq.sValEq as bs) : WordSemStackEq.sValEq (fr :: as) (fr :: bs) :=
  ⟨h, sFrameValEq_refl fr⟩

/-! ### `LASTN` transport along `sValEq`

Value-equality of stacks gives value-equality of every `LASTN` suffix, hence the
handler frame found by the pinned exception clause exists on the swapped side
with the same locals size and handler slot (values, not keys, transported). -/

theorem sValEq_append : ∀ (a a' b b' : List (WordSemStackFrame 64)),
    WordSemStackEq.sValEq a a' → WordSemStackEq.sValEq b b' →
    WordSemStackEq.sValEq (a ++ b) (a' ++ b')
  | [], [], b, b', _, h2 => h2
  | [], _ :: _, b, b', h1, _ => by cases h1
  | _ :: _, [], b, b', h1, _ => by cases h1
  | (a :: as), (a' :: as'), b, b', h1, h2 => by
      obtain ⟨hv, hf⟩ := h1
      exact ⟨sValEq_append as as' b b' hv h2, hf⟩

theorem sValEq_reverse : ∀ (a b : List (WordSemStackFrame 64)),
    WordSemStackEq.sValEq a b → WordSemStackEq.sValEq a.reverse b.reverse
  | [], [], _ => True.intro
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | (a :: as), (b :: bs), h => by
      obtain ⟨hv, hf⟩ := h
      simp only [List.reverse_cons]
      exact sValEq_append _ _ _ _ (sValEq_reverse as bs hv) ⟨True.intro, hf⟩

theorem sValEq_take : ∀ (a b : List (WordSemStackFrame 64)) (n : Nat),
    WordSemStackEq.sValEq a b → WordSemStackEq.sValEq (a.take n) (b.take n)
  | [], [], n, _ => by cases n <;> exact True.intro
  | [], _ :: _, n, h => by cases h
  | _ :: _, [], n, h => by cases h
  | (a :: as), (b :: bs), n, h => by
      obtain ⟨hv, hf⟩ := h
      cases n with
      | zero => exact True.intro
      | succ k => exact ⟨sValEq_take as bs k hv, hf⟩

theorem sValEq_lastN (a b : List (WordSemStackFrame 64))
    (h : WordSemStackEq.sValEq a b) (n : Nat) :
    WordSemStackEq.sValEq (wordSemLastN n a) (wordSemLastN n b) := by
  unfold wordSemLastN
  exact sValEq_reverse _ _ (sValEq_take _ _ n (sValEq_reverse _ _ h))

theorem sValEq_lastN_head (a b : List (WordSemStackFrame 64))
    (h : WordSemStackEq.sValEq a b) (n : Nat) (fr : WordSemStackFrame 64)
    (ls : List (WordSemStackFrame 64))
    (ha : wordSemLastN (n + 1) a = fr :: ls) :
    ∃ fr' ls', wordSemLastN (n + 1) b = fr' :: ls' ∧
      WordSemStackEq.sFrameValEq fr fr' := by
  have hh := sValEq_lastN a b h (n + 1)
  rw [ha] at hh
  cases hb : wordSemLastN (n + 1) b with
  | nil => rw [hb] at hh; cases hh
  | cons fr' ls' =>
      refine ⟨fr', ls', rfl, ?_⟩
      rw [hb] at hh
      exact hh.2


/-! ### Result transport along a value-equal stack swap

The pinned `stackSwapPost` transports every result except `error`; for the
exception case the handler frame is relocated with `sValEq_lastN_head`. -/

theorem evaluate_stack_swap_result_nonexception {C F : Type}
    (c : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) (res : Option (WordSemResult 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (h0 : res ≠ some (WordSemResult.error))
    (h1 : ∀ (l : WordLocW 64) (r : List (WordLocW 64)), res ≠ some (.result l r))
    (h2 : ∀ (l v : WordLocW 64), res ≠ some (.exception l v))
    (hev : evaluate c s = (res, middle)) :
    ∃ st, evaluate c { s with stack := xs } = (res, { middle with stack := st }) ∧
      WordSemStackEq.sValEq middle.stack st := by
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap c s
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  cases res with
  | none =>
      dsimp only [WordSemStackEq.stackSwapRel] at hT
      obtain ⟨-, -, hrun⟩ := hT
      obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
      exact ⟨st, hevT, hvalT⟩
  | some r =>
      cases r with
      | error => exact absurd rfl h0
      | result l rt =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨-, -, hrun⟩ := hT
          obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
          exact absurd rfl (h1 l rt)
      | exception l v => exact absurd rfl (h2 l v)
      | finalFfi e =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨hst, -, hrun⟩ := hT
          refine ⟨[], ?_, ?_⟩
          · rw [hrun xs hval, ← hst]
          · rw [hst]
            exact True.intro
      | timeOut =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨hst, -, hrun⟩ := hT
          refine ⟨[], ?_, ?_⟩
          · rw [hrun xs hval, ← hst]
          · rw [hst]
            exact True.intro
      | notEnoughSpace =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨hst, -, hrun⟩ := hT
          refine ⟨[], ?_, ?_⟩
          · rw [hrun xs hval, ← hst]
          · rw [hst]
            exact True.intro
      | «break» k =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨-, -, hrun⟩ := hT
          obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
          exact ⟨st, hevT, hvalT⟩
      | «continue» k =>
          dsimp only [WordSemStackEq.stackSwapRel] at hT
          obtain ⟨-, -, hrun⟩ := hT
          obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
          exact ⟨st, hevT, hvalT⟩

theorem evaluate_stack_swap_result_exception {C F : Type}
    (c : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) (location value : WordLocW 64)
    (middle : WordSemStateFiniteExact 64 C F)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hev : evaluate c s = (some (.exception location value), middle)) :
    ∃ (st : List (WordSemStackFrame 64)) (locs : Spt (WordLocW 64)),
      evaluate c { s with stack := xs } =
        (some (.exception location value),
          { middle with stack := st, handler := middle.handler, locals := locs }) := by
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap c s
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  obtain ⟨-, e0, e, n, ls, m, lss, hlastn, hm, -, -, hhandn, hforall⟩ := hT
  obtain ⟨fr', ls', hlastn', hframe⟩ :=
    sValEq_lastN_head s.stack xs hval s.handler
      (WordSemStackFrame.stackFrame m e0 e (some n)) ls hlastn
  obtain ⟨m', e0', e', y'⟩ := fr'
  rw [WordSemStackEq.sFrameValEqDef2] at hframe
  obtain ⟨-, hy, hm'⟩ := hframe
  rw [← hm', ← hy] at hlastn'
  obtain ⟨st, locs, hevT, -, -, -⟩ := hforall xs e0' e' ls' ⟨hlastn', hval⟩
  rw [← hhandn] at hevT
  refine ⟨st, locs, ?_⟩
  rw [show (fun ys => evaluate c { s with stack := ys }) xs = evaluate c { s with stack := xs }
    from rfl] at hevT
  exact hevT

/-! ### Driver cases (concrete reached states, pointwise IHs) -/

theorem wordPathWork_seq_sValEq_stack_variant {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (res : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (st : List (WordSemStackFrame 64))
    (hev : evaluate first s = (res, middle))
    (hevT : evaluate first { s with stack := xs } = (res, { middle with stack := st }))
    (hval : WordSemStackEq.sValEq middle.stack st)
    (ihF : wordPathWork first { s with stack := xs } = wordPathWork first s)
    (ihS : wordPathWork second
        { (fixClock s ((none : Option (WordSemResult 64)), middle)).2 with stack := st } =
      wordPathWork second (fixClock s ((none : Option (WordSemResult 64)), middle)).2)
    (hne : (evaluate (.seq first second) s).1 ≠ some (WordSemResult.error)) :
    wordPathWork (.seq first second) { s with stack := xs } =
      wordPathWork (.seq first second) s := by
  rw [wordPathWork, wordPathWork, ihF, hev, hevT, fixClock_swap_stack]
  simp only [fixClock, Prod.fst]
  cases res with
  | none =>
      exact congrArg (fun z => 1 + wordPathWork first s + z) ihS
  | some r => rfl

theorem wordPathWork_ite_sValEq_stack_variant {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs)
    (ih1 : wordPathWork first { s with stack := xs } = wordPathWork first s)
    (ih2 : wordPathWork second { s with stack := xs } = wordPathWork second s) :
    wordPathWork (.ite cmp reg operand first second) { s with stack := xs } =
      wordPathWork (.ite cmp reg operand first second) s := by
  rw [wordPathWork, wordPathWork, getVar_stack, getVarImm_stack]
  split <;> simp_all


/-! ### Driver cases with a zero tail (`some` result / non-`contLoop` result) -/

theorem wordPathWork_seq_sValEq_stack_variant_zero {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64))
    (res : Option (WordSemResult 64)) (middle mT : WordSemStateFiniteExact 64 C F)
    (hev : evaluate first s = (res, middle))
    (hevT : evaluate first { s with stack := xs } = (res, mT))
    (hne : res ≠ none)
    (ihF : wordPathWork first { s with stack := xs } = wordPathWork first s) :
    wordPathWork (.seq first second) { s with stack := xs } =
      wordPathWork (.seq first second) s := by
  rw [wordPathWork, wordPathWork, ihF, hev, hevT]
  cases res with
  | none => exact absurd rfl hne
  | some r => rfl

/-- Stack-swap transport for `.result` runs (the transport excluded by
`evaluate_stack_swap_result_nonexception`). -/
theorem evaluate_stack_swap_result_value {C F : Type}
    (c : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) (l0 : WordLocW 64) (r0 : List (WordLocW 64))
    (middle : WordSemStateFiniteExact 64 C F)
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hev : evaluate c s = (some (.result l0 r0), middle)) :
    ∃ st, evaluate c { s with stack := xs } = (some (.result l0 r0), { middle with stack := st }) ∧
      WordSemStackEq.sValEq middle.stack st := by
  have hT := Flapjack.WordSemStackEq.evaluateStackSwap c s
  rw [WordSemStackEq.stackSwapPost_iff, hev] at hT
  dsimp only [WordSemStackEq.stackSwapRel] at hT
  obtain ⟨-, -, hrun⟩ := hT
  obtain ⟨st, hevT, hvalT, -⟩ := hrun xs hval
  exact ⟨st, hevT, hvalT⟩

/-- `decClock` commutes with the stack swap. -/
theorem decClock_swap_stack {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64)) :
    decClock { s with stack := xs } = { decClock s with stack := xs } := by
  cases s
  rfl

/-- Tail of the loop clause at the stop state: swapping the stack under `decClock`
does not change the cost, so the clock-guarded tail of the transported run equals the
clock-guarded tail of the source run. -/
theorem wordPathWork_stop_tail {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (m : WordSemStateFiniteExact 64 C F) (st : List (WordSemStackFrame 64))
    (ihStop : wordPathWork (wordSemSTOP p) { decClock m with stack := st } =
      wordPathWork (wordSemSTOP p) (decClock m)) :
    (if _hc : m.clock = 0 then 0
     else wordPathWork (wordSemSTOP p) (decClock { m with stack := st })) =
    (if _hc : m.clock = 0 then 0
     else wordPathWork (wordSemSTOP p) (decClock m)) := by
  by_cases hc : m.clock = 0
  · rw [dif_pos hc, dif_pos hc]
  · rw [dif_neg hc, dif_neg hc, decClock_swap_stack]
    exact ihStop

/-! ### The guarded well-founded driver

`.call` is supplied as the explicit hypothesis `hcall` (the one remaining
obligation); every other constructor is discharged here, including the
`cutState`-guarded `.loop` case and the `fixClock`-guarded `.seq`/`.ite`
cases, with every recursive call made at the reached child state.
-/

theorem wordPathWork_stack_variant_dispatch {C F : Type}
    (hcall : ∀ (ret : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat))
      (dest : Option Nat) (args : List Nat)
      (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
      (s : WordSemStateFiniteExact 64 C F) (xs : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq s.stack xs →
      (evaluate (.call ret dest args handler) s).1 ≠ some WordSemResult.error →
      wordPathWork (.call ret dest args handler) { s with stack := xs } =
        wordPathWork (.call ret dest args handler) s) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
      (xs : List (WordSemStackFrame 64)),
      WordSemStackEq.sValEq s.stack xs →
      (evaluate p s).1 ≠ some WordSemResult.error →
      wordPathWork p { s with stack := xs } = wordPathWork p s := by
  intro p s xs hval hne
  match p, s, xs, hval, hne with
  | .seq first second, s, xs, hval, hne =>
      rcases hev : evaluate first s with ⟨res, middle⟩
      have hfixS : fixClock s (evaluate first s) = (res, middle) := by
        rw [← hev]; exact fix_clock_evaluate s first
      have hfcS1 : middle.clock ≤ s.clock :=
        (fixClock_IMP_LESS_EQ s res middle (evaluate first s) hfixS).1
      have hfcS2 : middle.termdep = s.termdep :=
        (fixClock_IMP_LESS_EQ s res middle (evaluate first s) hfixS).2
      have hneF : (evaluate first s).1 ≠ some WordSemResult.error := by
        intro hc
        exact hne (evaluate_seq_error_fst first second s hc)
      have ihF : wordPathWork first { s with stack := xs } = wordPathWork first s :=
        wordPathWork_stack_variant_dispatch hcall first s xs hval hneF
      cases res with
      | none =>
          obtain ⟨st, hevT, hvalT⟩ :=
            evaluate_stack_swap_result_nonexception first s xs none middle hval
              (by simp) (by simp) (by simp) hev
          have hfe' : (s.fixClock (evaluate first s)).2 = middle :=
            (congrArg Prod.snd (fix_clock_evaluate s first)).trans (by rw [hev])
          have hfe : (fixClock s ((none : Option (WordSemResult 64)), middle)).2 = middle := by
            rw [← hev]; exact hfe'
          have hneS : (evaluate second middle).1 ≠ some WordSemResult.error := by
            intro hc
            exact hne (evaluate_seq_error_snd first second s (by rw [hev])
              (by rw [hfe']; exact hc))
          have ihS_raw : wordPathWork second { middle with stack := st } =
              wordPathWork second middle :=
            wordPathWork_stack_variant_dispatch hcall second middle st hvalT hneS
          have ihS : wordPathWork second
              { (fixClock s ((none : Option (WordSemResult 64)), middle)).2 with stack := st } =
              wordPathWork second (fixClock s ((none : Option (WordSemResult 64)), middle)).2 := by
            rw [hfe]; exact ihS_raw
          exact wordPathWork_seq_sValEq_stack_variant first second s xs none middle st
            hev hevT hvalT ihF ihS hne
      | some r =>
          cases r with
          | error => exact (hneF (by rw [hev])).elim
          | exception l' v =>
              obtain ⟨st0, locs0, hevEx⟩ :=
                evaluate_stack_swap_result_exception first s xs l' v middle hval hev
              obtain ⟨mT, hevT⟩ : ∃ mT, evaluate first { s with stack := xs } =
                  (some (.exception l' v), mT) := ⟨_, hevEx⟩
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some (.exception l' v)) middle mT hev hevT (by simp) ihF
          | result l' r' =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_value first s xs l' r' middle hval hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some (.result l' r')) middle { middle with stack := st } hev hevT (by simp) ihF
          | finalFfi e =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_nonexception first s xs (some (.finalFfi e))
                  middle hval (by simp) (by simp) (by simp) hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some (.finalFfi e)) middle { middle with stack := st } hev hevT (by simp) ihF
          | timeOut =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_nonexception first s xs (some .timeOut)
                  middle hval (by simp) (by simp) (by simp) hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some .timeOut) middle { middle with stack := st } hev hevT (by simp) ihF
          | notEnoughSpace =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_nonexception first s xs (some .notEnoughSpace)
                  middle hval (by simp) (by simp) (by simp) hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some .notEnoughSpace) middle { middle with stack := st } hev hevT (by simp) ihF
          | «break» k =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_nonexception first s xs (some (.break k))
                  middle hval (by simp) (by simp) (by simp) hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some (.break k)) middle { middle with stack := st } hev hevT (by simp) ihF
          | «continue» k =>
              obtain ⟨st, hevT, -⟩ :=
                evaluate_stack_swap_result_nonexception first s xs (some (.continue k))
                  middle hval (by simp) (by simp) (by simp) hev
              exact wordPathWork_seq_sValEq_stack_variant_zero first second s xs
                (some (.continue k)) middle { middle with stack := st } hev hevT (by simp) ihF
  | .ite cmp reg operand first second, s, xs, hval, hne =>
      rw [wordPathWork, wordPathWork, getVar_stack, getVarImm_stack]
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
                  | true =>
                      simp only [hx, hy, hc]
                      have hne1 : (evaluate first s).1 ≠ some WordSemResult.error := by
                        intro h
                        exact hne (evaluate_ite_error_true cmp reg operand first second s x y hx hy hc h)
                      rw [wordPathWork_stack_variant_dispatch hcall first s xs hval hne1]
                  | false =>
                      simp only [hx, hy, hc]
                      have hne2 : (evaluate second s).1 ≠ some WordSemResult.error := by
                        intro h
                        exact hne (evaluate_ite_error_false cmp reg operand first second s x y hx hy hc h)
                      rw [wordPathWork_stack_variant_dispatch hcall second s xs hval hne2]
  | .loop names body exitNames, s, xs, hval, hne =>
      rw [wordPathWork, wordPathWork]
      cases hs : cutState (names, .ln) s with
      | none =>
          rw [cutState_stack_none (names, .ln) s xs hs]
      | some cs =>
          rw [cutState_stack_some (names, .ln) s xs cs hs]
          simp only []
          obtain ⟨l, hl⟩ := cutStateConst (names, .ln) s cs hs
          have hvalCs : WordSemStackEq.sValEq cs.stack xs := by
            rw [show cs.stack = s.stack from by rw [hl]]; exact hval
          rw [fix_clock_evaluate cs body, fix_clock_evaluate { cs with stack := xs } body]
          rcases hev : evaluate body cs with ⟨res, s1⟩
          have hcs1 : cs.clock = s.clock := (cutState_clock_termdep (names, .ln) s cs hs).1
          have hcs2 : cs.termdep = s.termdep := (cutState_clock_termdep (names, .ln) s cs hs).2
          have hfixB : fixClock cs (evaluate body cs) = (res, s1) := by
            rw [← hev]; exact fix_clock_evaluate cs body
          have hfcB1 : s1.clock ≤ cs.clock :=
            (fixClock_IMP_LESS_EQ cs res s1 (evaluate body cs) hfixB).1
          have hfcB2 : s1.termdep = cs.termdep :=
            (fixClock_IMP_LESS_EQ cs res s1 (evaluate body cs) hfixB).2
          have hcs1 : cs.clock = s.clock := (cutState_clock_termdep (names, .ln) s cs hs).1
          have hcs2 : cs.termdep = s.termdep := (cutState_clock_termdep (names, .ln) s cs hs).2
          have hfixB : fixClock cs (evaluate body cs) = (res, s1) := by
            rw [← hev]; exact fix_clock_evaluate cs body
          have hfcB1 : s1.clock ≤ cs.clock :=
            (fixClock_IMP_LESS_EQ cs res s1 (evaluate body cs) hfixB).1
          have hfcB2 : s1.termdep = cs.termdep :=
            (fixClock_IMP_LESS_EQ cs res s1 (evaluate body cs) hfixB).2
          have hneB : (evaluate body cs).1 ≠ some WordSemResult.error := by
            intro hc
            exact hne (evaluate_loop_error_body names body exitNames s cs hs hc)
          have ihB : wordPathWork body { cs with stack := xs } = wordPathWork body cs :=
            wordPathWork_stack_variant_dispatch hcall body cs xs hvalCs hneB
          cases res with
          | none =>
              obtain ⟨st, hevT, hvalT⟩ :=
                evaluate_stack_swap_result_nonexception body cs xs none s1 hvalCs
                  (by simp) (by simp) (by simp) hev
              simp only [hevT, ihB, wordSemContLoop, if_true]
              try rw [show ({ s1 with stack := st } : WordSemStateFiniteExact 64 C F).clock = s1.clock from rfl]
              by_cases hc0 : s1.clock = 0
              · rw [dif_pos hc0, dif_pos hc0]
              · rw [dif_neg hc0, dif_neg hc0]
                have ihStop : wordPathWork (wordSemSTOP (.loop names body exitNames))
                    { decClock s1 with stack := st } =
                    wordPathWork (wordSemSTOP (.loop names body exitNames)) (decClock s1) := by
                  refine wordPathWork_stack_variant_dispatch hcall
                    (wordSemSTOP (.loop names body exitNames)) (decClock s1) st ?_ ?_
                  · rw [show (decClock s1).stack = s1.stack from rfl]; exact hvalT
                  · intro hc
                    exact hne (evaluate_loop_error_stop names body exitNames s cs hs none s1 hfixB
                      (by simp [wordSemContLoop]) hc0 hc)
                rw [decClock_swap_stack]
                exact congrArg (fun z => 1 + wordPathWork body cs + z) ihStop
          | some r =>
              cases r with
              | error => exact (hneB (by rw [hev])).elim
              | exception l' v =>
                  obtain ⟨st0, locs0, hevEx⟩ :=
                    evaluate_stack_swap_result_exception body cs xs l' v s1 hvalCs hev
                  obtain ⟨mT, hevT⟩ : ∃ mT, evaluate body { cs with stack := xs } =
                      (some (.exception l' v), mT) := ⟨_, hevEx⟩
                  simp [hevT, ihB, wordSemContLoop]
              | result l' r' =>
                  obtain ⟨st, hevT, -⟩ :=
                    evaluate_stack_swap_result_value body cs xs l' r' s1 hvalCs hev
                  simp [hevT, ihB, wordSemContLoop]
              | finalFfi e =>
                  obtain ⟨st, hevT, -⟩ :=
                    evaluate_stack_swap_result_nonexception body cs xs (some (.finalFfi e)) s1 hvalCs
                      (by simp) (by simp) (by simp) hev
                  simp [hevT, ihB, wordSemContLoop]
              | timeOut =>
                  obtain ⟨st, hevT, -⟩ :=
                    evaluate_stack_swap_result_nonexception body cs xs (some .timeOut) s1 hvalCs
                      (by simp) (by simp) (by simp) hev
                  simp [hevT, ihB, wordSemContLoop]
              | notEnoughSpace =>
                  obtain ⟨st, hevT, -⟩ :=
                    evaluate_stack_swap_result_nonexception body cs xs (some .notEnoughSpace) s1 hvalCs
                      (by simp) (by simp) (by simp) hev
                  simp [hevT, ihB, wordSemContLoop]
              | «break» k =>
                  obtain ⟨st, hevT, -⟩ :=
                    evaluate_stack_swap_result_nonexception body cs xs (some (.break k)) s1 hvalCs
                      (by simp) (by simp) (by simp) hev
                  simp [hevT, ihB, wordSemContLoop]
              | «continue» k =>
                  obtain ⟨st, hevT, hvalT⟩ :=
                    evaluate_stack_swap_result_nonexception body cs xs (some (.continue k)) s1 hvalCs
                      (by simp) (by simp) (by simp) hev
                  by_cases hk : k = 0
                  · subst hk
                    simp only [hevT, ihB, wordSemContLoop]
                    try rw [show ({ s1 with stack := st } : WordSemStateFiniteExact 64 C F).clock = s1.clock from rfl]
                    by_cases hc0 : s1.clock = 0
                    · rw [dif_pos hc0, dif_pos hc0]
                    · rw [dif_neg hc0, dif_neg hc0]
                      have ihStop : wordPathWork (wordSemSTOP (.loop names body exitNames))
                          { decClock s1 with stack := st } =
                          wordPathWork (wordSemSTOP (.loop names body exitNames)) (decClock s1) := by
                        refine wordPathWork_stack_variant_dispatch hcall
                          (wordSemSTOP (.loop names body exitNames)) (decClock s1) st ?_ ?_
                        · rw [show (decClock s1).stack = s1.stack from rfl]; exact hvalT
                        · intro hc
                          exact hne (evaluate_loop_error_stop names body exitNames s cs hs
                            (some (.continue 0)) s1 hfixB (by simp [wordSemContLoop]) hc0 hc)
                      rw [decClock_swap_stack]
                      exact congrArg (fun z => 1 + wordPathWork body cs + z) ihStop
                  · simp [hevT, ihB, wordSemContLoop, hk]
  | .call ret dest args handler, s, xs, hval, hne =>
      exact hcall ret dest args handler s xs hval hne
  | .mustTerminate _, _, _, _, _ => simp only [wordPathWork]
  | .skip, _, _, _, _ => simp only [wordPathWork]
  | .move _ _, _, _, _, _ => simp only [wordPathWork]
  | .inst _, _, _, _, _ => simp only [wordPathWork]
  | .assign _ _, _, _, _, _ => simp only [wordPathWork]
  | .get _ _, _, _, _, _ => simp only [wordPathWork]
  | .set _ _, _, _, _, _ => simp only [wordPathWork]
  | .store _ _, _, _, _, _ => simp only [wordPathWork]
  | .tick, _, _, _, _ => simp only [wordPathWork]
  | .storeConsts _ _ _ _ _, _, _, _, _ => simp only [wordPathWork]
  | .return _ _, _, _, _, _ => simp only [wordPathWork]
  | .break _, _, _, _, _ => simp only [wordPathWork]
  | .continue _, _, _, _, _ => simp only [wordPathWork]
  | .opCurrHeap _ _ _, _, _, _, _ => simp only [wordPathWork]
  | .locValue _ _, _, _, _, _ => simp only [wordPathWork]
  | .install _ _ _ _ _, _, _, _, _ => simp only [wordPathWork]
  | .codeBufferWrite _ _, _, _, _, _ => simp only [wordPathWork]
  | .dataBufferWrite _ _, _, _, _, _ => simp only [wordPathWork]
  | .ffi _ _ _ _ _ _, _, _, _, _ => simp only [wordPathWork]
  | .shareInst _ _ _, _, _, _, _ => simp only [wordPathWork]
  | .alloc _ _, _, _, _, _ => simp only [wordPathWork]
  | .raise _, _, _, _, _ => simp only [wordPathWork]
  termination_by p s xs => (s.termdep, s.clock, sizeOf p)
  decreasing_by
    all_goals
      simp_wf
      apply wordSemLex
      try (rcases hc with ⟨_, _⟩)
      try (rcases hcl with ⟨_, _⟩)
      try simp +zetaDelta only [Flapjack.WordSemStateFiniteExact.decClock,
        Flapjack.WordSemStateFiniteExact.callEnv, Flapjack.WordSemStateFiniteExact.setVars,
        Flapjack.WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep, true_and] at *
      first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, Or.inl (by omega)⟩)
      | (right; refine ⟨by omega, Or.inr ⟨by omega, by decreasing_tactic⟩⟩)
end InitECandidate.Runtime.WordToStack
