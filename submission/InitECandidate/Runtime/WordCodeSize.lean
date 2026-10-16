import InitECandidate.Runtime.WordWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Fixed Word procedure sizes together with the semantic no-install property. -/
structure WordCodeSize {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (s : WordSemStateFiniteExact width C F) : Prop where
  code : ∀ key arity body, sptLookup key s.code = some (arity,body) → sizeOf body ≤ limit
  noInstall : WordProps.noInstallCode s.code

theorem WordCodeSize.of_code_eq {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s next : WordSemStateFiniteExact width C F}
    (bounded : WordCodeSize limit s) (same : next.code = s.code) : WordCodeSize limit next := by
  constructor
  · intro key arity body found
    rw [same] at found
    exact bounded.code key arity body found
  · rw [same]
    exact bounded.noInstall

/-- The original evaluator's no-install theorem preserves the exact code map. -/
theorem WordCodeSize.evaluated {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F}
    (bounded : WordCodeSize limit s) (p : WordLangProgHOL (BitVec width))
    (safe : noInstallSubprogsHOL p = true) :
    WordCodeSize limit (fixClock s (evaluate p s)).2 := by
  apply bounded.of_code_eq
  exact Flapjack.WordSemStateFiniteExact.code_evaluate p s safe bounded.noInstall

/-- Both direct and indirect code lookup select a bounded no-install body. -/
theorem WordCodeSize.findCode {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F}
    (bounded : WordCodeSize limit s) (dest : Option Nat) (args foundArgs : List (WordLocW width))
    (body : WordLangProgHOL (BitVec width)) (stackSize : Option Nat)
    (found : wordSemFindCode dest args s.code s.stackSize = some (foundArgs,body,stackSize)) :
    sizeOf body ≤ limit ∧ noInstallSubprogsHOL body = true := by
  obtain ⟨key,arity,lookup⟩ := WordProps.findCode_lookup s.code dest args s.stackSize foundArgs body stackSize found
  exact ⟨bounded.code key arity body lookup, bounded.noInstall key arity body lookup⟩

theorem WordCodeSize.callEnv {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F}
    (bounded : WordCodeSize limit s) (args : List (WordLocW width)) (size : Option Nat) :
    WordCodeSize limit (callEnv args size s) := bounded.of_code_eq rfl

theorem WordCodeSize.decClock {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s) :
    WordCodeSize limit (decClock s) := bounded.of_code_eq rfl

theorem WordCodeSize.pushEnv {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s)
    (env : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    WordCodeSize limit (pushEnv env handler s) := bounded.of_code_eq (Flapjack.WordSemStateFiniteExact.code_pushEnv env handler s)

theorem WordCodeSize.cutState {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s next : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s)
    (names : WordLangCutsetsHOL) (cut : cutState names s = some next) : WordCodeSize limit next := by
  apply bounded.of_code_eq
  unfold Flapjack.WordSemStateFiniteExact.cutState at cut
  split at cut
  · cases cut
  · cases cut
    rfl

theorem WordCodeSize.popEnv {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s next : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s)
    (popped : popEnv s = some next) : WordCodeSize limit next := by
  apply bounded.of_code_eq
  unfold Flapjack.WordSemStateFiniteExact.popEnv at popped
  split at popped
  · cases popped
    rfl
  · cases popped
    rfl
  · cases popped

theorem WordCodeSize.setVar {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s)
    (reg : Nat) (value : WordLocW width) : WordCodeSize limit (setVar reg value s) :=
  bounded.of_code_eq rfl

theorem WordCodeSize.setVars {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : WordSemStateFiniteExact width C F} (bounded : WordCodeSize limit s)
    (regs : List Nat) (values : List (WordLocW width)) : WordCodeSize limit (setVars regs values s) :=
  bounded.of_code_eq rfl

#print axioms WordCodeSize.evaluated
#print axioms WordCodeSize.findCode
#print axioms WordCodeSize.cutState
#print axioms WordCodeSize.popEnv
end InitECandidate.Runtime.WordToStack
