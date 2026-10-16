import InitECandidate.Runtime.StackAllocFreeState
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect

/-- Uniform procedure-size bounds on both installed code and every oracle entry. -/
structure CodeSizeState {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (s : StackSemStateFiniteExact width C F) : Prop where
  code : ∀ key body, sptLookup key s.code = some body → sizeOf body ≤ limit
  oracle : ∀ n key body, (key, body) ∈ (s.compileOracle n).2.1 → sizeOf body ≤ limit

/-- The original code/oracle evolution theorem preserves the numerical bound,
including dynamic installation. No target evaluation or no-install premise is needed. -/
theorem CodeSizeState.of_evaluate {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {p : HolProg width} {s t : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)}
    (run : StackSemEvaluate.evaluate (p, s) = (result, t)) (bounded : CodeSizeState limit s) :
    CodeSizeState limit t := by
  obtain ⟨count, oracle, code, _⟩ :=
    Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p s result t run
  constructor
  · intro key body lookup
    rw [code] at lookup
    rcases sptLookup_foldl_sptUnion _ _ _ _ lookup with old | ⟨tree, member, lookup⟩
    · exact bounded.code key body old
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      rw [sptLookup_sptFromAList] at lookup
      exact bounded.oracle index key body (sptAListLookup_mem _ _ _ lookup)
  · intro n key body member
    rw [oracle] at member
    exact bounded.oracle (n + count) key body member

theorem CodeSizeState.withClock {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : StackSemStateFiniteExact width C F} (bounded : CodeSizeState limit s) (fuel : Nat) :
    CodeSizeState limit {s with clock := fuel} := ⟨bounded.code, bounded.oracle⟩

theorem CodeSizeState.decClock {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : StackSemStateFiniteExact width C F} (bounded : CodeSizeState limit s) :
    CodeSizeState limit (decClock s) := ⟨bounded.code, bounded.oracle⟩

theorem CodeSizeState.setVar {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : StackSemStateFiniteExact width C F} (bounded : CodeSizeState limit s)
    (register : Nat) (value : WordLocW width) :
    CodeSizeState limit (Flapjack.StackSemStateOps.setVar register value s) :=
  ⟨bounded.code, bounded.oracle⟩

theorem CodeSizeState.fixClock {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {initial returned : StackSemStateFiniteExact width C F}
    (bounded : CodeSizeState limit returned) (result : Option (StackSemResult width)) :
    CodeSizeState limit (fixClock initial (result, returned)).2 := ⟨bounded.code, bounded.oracle⟩

/-- Direct and indirect calls select an already bounded code-tree procedure. -/
theorem findCode_size {width : Nat} [NeZero width] {C F : Type} {limit : Nat}
    (s : StackSemStateFiniteExact width C F) (bounded : CodeSizeState limit s)
    (destination : Sum Nat Nat) (registers : HolFiniteMapExact Nat (WordLocW width))
    (body : HolProg width) (found : findCode destination registers s.code = some body) :
    sizeOf body ≤ limit := by
  cases destination with
  | inl label => exact bounded.code label body found
  | inr register =>
    simp only [findCode] at found
    split at found
    · exact bounded.code _ body found
    · cases found

/-- A finite size ceiling for a concrete finite code list. -/
noncomputable def codeSizeLimit {width : Nat} [NeZero width] (code : List (Nat × HolProg width)) : Nat :=
  code.foldr (fun entry rest => max (sizeOf entry.2) rest) 0

theorem member_size_le_codeSizeLimit {width : Nat} [NeZero width]
    (code : List (Nat × HolProg width)) (key : Nat) (body : HolProg width)
    (member : (key, body) ∈ code) : sizeOf body ≤ codeSizeLimit code := by
  induction code with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Concrete code and oracle list certificates establish the runtime invariant. -/
theorem CodeSizeState.of_lists {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (s : StackSemStateFiniteExact width C F) (code : List (Nat × HolProg width))
    (codeEq : s.code = sptFromAList code) (codeBound : codeSizeLimit code ≤ limit)
    (oracleBound : ∀ n, codeSizeLimit (s.compileOracle n).2.1 ≤ limit) : CodeSizeState limit s := by
  constructor
  · intro key body found
    rw [codeEq, sptLookup_sptFromAList] at found
    exact Nat.le_trans (member_size_le_codeSizeLimit code key body
      (sptAListLookup_mem _ _ _ found)) codeBound
  · intro n key body member
    exact Nat.le_trans (member_size_le_codeSizeLimit _ key body member) (oracleBound n)

#print axioms CodeSizeState.of_lists

#print axioms CodeSizeState.of_evaluate
#print axioms findCode_size
end InitECandidate.Runtime.StackToLab
