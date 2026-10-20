import InitECandidate.Runtime.WordPathWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap

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
end InitECandidate.Runtime.WordToStack
