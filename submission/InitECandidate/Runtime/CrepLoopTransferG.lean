import InitECandidate.Runtime.CrepLoopLeafG
import InitECandidate.Runtime.CrepWorkF
import InitECandidate.Runtime.SourceCostLoopTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! Crep-to-Loop transfer at a generic Loop pricing, in the Loop function
whose label `crep_to_loop` assigns to the running Crep function. -/

/-- The Loop label `crep_to_loop` gives a Crep function: its `funcs` entry
(as `findLabExact`). -/
def labOf (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) (fn : CName) : Nat :=
  match funcs.lookup fn with
  | some (label, _) => label
  | none => 0

theorem findLabExact_labOf (context : CrepToLoopContextExact) (fn : CName) :
    findLabExact context fn = labOf context.funcs fn := rfl

/-- The compiled Loop run in function `f`, at a clock extension for which all
original simulation conclusions hold, does at most `w` work at leaf price `L`. -/
def LoopPaidG (L : LeafPrice) (f : Nat) {F : Type} (context : CrepToLoopContextExact) (live : NumSet)
    (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) (p : CrepProgHOL 64)
    (w : Nat) : Prop :=
  ∃ extra wl,
    LoopWorkG L f { u with clock := u.clock + extra } (compileHOLExact context live p)
      (evaluate (compileHOLExact context live p) { u with clock := u.clock + extra }) wl ∧
    wl ≤ w ∧
    LoopRunRel context live (evalCrepSemHOLProgExact t p)
      (evaluate (compileHOLExact context live p) { u with clock := u.clock + extra })

/-- Crep prices that pay for a generic Loop pricing. Call prices are per
(caller, callee, return-name count), with caller and callee mapped to their
Loop labels through `funcs`; `shortP` pays a call stopping before its callee. -/
structure CrepFitG (P : LoopPricingG) (unit prim ret shortP : Nat) (callP : CName → CName → Nat → Nat)
    (funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)) : Prop where
  iteOk : P.L.ite ≤ unit
  iterOk : P.L.iter ≤ unit
  retOk : P.L.ret ≤ ret
  /-- Argument passing is within the per-argument move charge. -/
  argOk : ∀ n, P.L.argCost n ≤ 39 * n
  tickOk : P.tickC ≤ unit
  breakOk : P.breakC ≤ unit
  contOk : P.contC ≤ unit
  ffiOk : P.ffiC ≤ unit
  raiseOk : P.constC + P.raiseC ≤ prim + 1
  setOk : P.setC ≤ unit
  shareOk : P.shareC ≤ unit
  storeOk : P.storeC ≤ unit
  store32Ok : P.store32C ≤ unit
  returnOk : P.returnC ≤ unit
  primOk : P.primC ≤ prim
  /-- A matched handler's dispatch: comparison and tick. -/
  handleOk : P.L.ite + P.tickC ≤ ret
  /-- An unmatched or absent handler re-raises (an exception pays three payload words). -/
  raiseRetOk : P.L.ite + P.raiseC ≤ 3 * ret
  /-- Return-name surcharges are for `n` names, or for the single fallback name
  `crep_to_loop` uses when the names are not all locals. -/
  callOk : ∀ fn g n, P.L.call + P.L.cont + P.L.cs (labOf funcs fn) (labOf funcs g) + P.L.ts (labOf funcs g) + P.L.rn n +
    P.L.rn 1 ≤ callP fn g n
  shortOk : P.L.shortC ≤ shortP

/-- Crep work priced by a generic Loop pricing. -/
abbrev CrepWorkG (P : LoopPricingG) (unit prim : Nat) (callP : CName → CName → Nat → Nat) (shortP ret : Nat)
    {σ : Type} := @CrepWorkF P.price P.priceList unit prim callP shortP ret σ

/-- Static Crep price of the non-recursive statements, as charged by `CrepWorkG`. -/
def crepLeafPriceG (P : LoopPricingG) (unit prim : Nat) : CrepProgHOL 64 → Option Nat
  | .skip => some 0
  | .tick | .break _ | .continue _ | .extCall _ _ _ _ _ => some unit
  | .raise _ => some (prim + 1)
  | .assign _ value => some (P.price value)
  | .storeGlob _ value | .shMem _ _ value => some (unit + P.price value)
  | .store address value | .store32 address value | .storeByte address value =>
      some (unit + P.price address + P.price value)
  | .return values => some (unit + P.priceList values + values.length)
  | .primitive names _ args => some (prim + names.length + args.length)
  | _ => none

theorem CrepFitG.leaf {P : LoopPricingG} {unit prim ret shortP : Nat} {callP : CName → CName → Nat → Nat}
    {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG P unit prim ret shortP callP funcs) {p : CrepProgHOL 64} {c : Nat}
    (leaf : crepLeafPriceG P unit prim p = some c) : ∃ k, P.leafPrice p = some k ∧ k ≤ c := by
  have := fit.tickOk; have := fit.breakOk; have := fit.contOk; have := fit.ffiOk; have := fit.raiseOk
  have := fit.setOk; have := fit.shareOk; have := fit.storeOk; have := fit.store32Ok
  have := fit.returnOk; have := fit.primOk
  cases p <;> simp [crepLeafPriceG] at leaf <;> subst leaf <;>
    simp only [LoopPricingG.leafPrice, Option.some.injEq, exists_eq_left'] <;> omega

/-- Generated expression code followed by an arbitrary continuation, at an
allowance. -/
theorem CodeAllowance.run_append {L : LeafPrice} (A : CodeAllowance L) {F : Type} (f : Nat) :
    ∀ (codes rest : List (HolLoopProg 64)) (c : Nat)
    (s middle : LoopSemStateFiniteExact 64 F)
    (output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) (wr : Nat),
    A.works codes = some c →
    evaluate (loopNestedSeqHOL codes) s = (none, middle) →
    LoopWorkG L f middle (loopNestedSeqHOL rest) output wr →
    ∃ w, LoopWorkG L f s (loopNestedSeqHOL (codes ++ rest)) output w ∧ w ≤ c + wr
  | [], rest, c, s, middle, output, wr, h, run, tail => by
    simp [CodeAllowance.works] at h
    subst h
    rw [loopNestedSeqHOL, evaluate] at run
    cases run
    exact ⟨wr, by simpa using tail, by omega⟩
  | head :: codes, rest, c, s, middle, output, wr, h, run, tail => by
    simp only [CodeAllowance.works] at h
    cases ha : A.work head <;> cases hb : A.works codes <;> simp_all
    rename_i a b
    subst h
    rw [loopNestedSeqHOL, evaluate_seq] at run
    rcases hx : evaluate head s with ⟨r1, s1⟩
    rw [hx] at run
    rcases r1 with _ | r1
    · simp only at run
      obtain ⟨wx, workx, boundx⟩ := A.sound head a ha F f s
      rw [hx] at workx
      obtain ⟨w', work', bound'⟩ := A.run_append f codes rest b s1 middle output wr hb run tail
      refine ⟨wx + w', ?_, by omega⟩
      rw [loopNestedSeqHOL]
      exact LoopWorkG.seqNext workx work'
    · simp at run

theorem CodeAllowance.works_append {L : LeafPrice} (A : CodeAllowance L) : ∀ (l r : List (HolLoopProg 64)),
    A.works (l ++ r) = (do
      let a ← A.works l
      let b ← A.works r
      pure (a + b))
  | [], r => by simp [CodeAllowance.works]
  | p :: l, r => by
    simp only [List.cons_append, CodeAllowance.works, A.works_append l r]
    cases A.work p <;> cases A.works l <;> cases A.works r <;> simp [Nat.add_assoc]

/-- Generated expression code alone is within its allowance. -/
theorem CodeAllowance.nested {L : LeafPrice} (A : CodeAllowance L) (codes : List (HolLoopProg 64)) (c : Nat)
    (h : A.works codes = some c) : LoopBoundedG L (loopNestedSeqHOL codes) c := by
  have := A.codes_append codes [] c 0 h (LoopBoundedG.leaf L.skip (Nat.le_refl 0))
  simpa using this

/-- Leaves: the pinned `ncompile_correct` supplies the run and relations; the
state-uniform compiled-code bound supplies the work, in any function. -/
theorem leaf_loop_paidG (P : LoopPricingG) {unit prim ret shortP : Nat} {callP : CName → CName → Nat → Nat}
    {funcs : HolFiniteMapExact Basis.Pure.MlString.MlString (Nat × Nat)}
    (fit : CrepFitG P unit prim ret shortP callP funcs) (f : Nat) {F : Type}
    {context : CrepToLoopContextExact} {live : NumSet}
    {t : CrepSemHOLState 64 F} {u : LoopSemStateFiniteExact 64 F} {p : CrepProgHOL 64}
    {w : Nat} (leaf : crepLeafPriceG P unit prim p = some w)
    (ok : (evalCrepSemHOLProgExact t p).1 ≠ some .error)
    (rel : CrepLoopRel context live t u) : LoopPaidG P.L f context live t u p w := by
  obtain ⟨k, hk, hle⟩ := fit.leaf leaf
  obtain ⟨extra, res1, t1, run, hs, hm, hg, hc, hr, hl⟩ :=
    crepToLoop_ncompile_correct p t _ _ u context live
      ⟨rfl, ok, rel.state, rel.memory, rel.globals, rel.code, rel.locals⟩
  obtain ⟨wl, work, bound⟩ := P.leaf_compile context live p k hk F f
    { u with clock := u.clock + extra }
  refine ⟨extra, wl, work, by omega, ?_⟩
  rw [run]
  exact ⟨hs, hm, hg, hc, hr, hl⟩

#print axioms findLabExact_labOf
#print axioms CrepFitG.leaf
#print axioms CodeAllowance.run_append
#print axioms CodeAllowance.nested
#print axioms CodeAllowance.works_append
#print axioms leaf_loop_paidG
end InitECandidate.Runtime.FineCost
