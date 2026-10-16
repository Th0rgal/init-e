import InitECandidate.Runtime.StackBitmapInvariant
import InitECandidate.Runtime.StackWorkCeiling
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open StackToLab

/-- A fixed bound on bitmap-copy leaf overhead, maintained at recursive sites. -/
structure BitmapBudget {width : Nat} [NeZero width] {C F : Type}
    (scale : Nat) (s : StackSemStateFiniteExact width C F) : Prop where
  oracle : EmptyBitmapOracle s
  leaf : 2 + (2 ^ width + 1) * s.bitmaps.length ≤ 2 * scale

theorem BitmapBudget.positive {width : Nat} [NeZero width] {C F : Type}
    {scale : Nat} {s : StackSemStateFiniteExact width C F} (bounded : BitmapBudget scale s) :
    1 ≤ scale := by have h := bounded.leaf; omega

theorem BitmapBudget.evaluated {width : Nat} [NeZero width] {C F : Type}
    {scale : Nat} {s : StackSemStateFiniteExact width C F} (bounded : BitmapBudget scale s)
    (p : HolProg width) : BitmapBudget scale (fixClock s (StackSemEvaluate.evaluate (p,s))).2 := by
  have next := bounded.oracle.of_evaluate (p := p) (s := s) (post := (StackSemEvaluate.evaluate (p,s)).2) (result := (StackSemEvaluate.evaluate (p,s)).1) rfl
  constructor
  · exact ⟨next.1.empty⟩
  · change 2 + (2 ^ width + 1) * (StackSemEvaluate.evaluate (p,s)).2.bitmaps.length ≤ _
    rw [next.2]
    exact bounded.leaf

theorem BitmapBudget.decClock {width : Nat} [NeZero width] {C F : Type}
    {scale : Nat} {s : StackSemStateFiniteExact width C F} (bounded : BitmapBudget scale s) :
    BitmapBudget scale (decClock s) := ⟨⟨bounded.oracle.empty⟩, bounded.leaf⟩

theorem BitmapBudget.setVar {width : Nat} [NeZero width] {C F : Type}
    {scale : Nat} {s : StackSemStateFiniteExact width C F} (bounded : BitmapBudget scale s)
    (r : Nat) (v : WordLocW width) : BitmapBudget scale (setVar r v s) :=
  ⟨⟨bounded.oracle.empty⟩, bounded.leaf⟩

/-- A fixed bitmap factor scales the already bounded conservative control work. -/
theorem removeWork_scaled {width : Nat} [NeZero width] {C F : Type}
    (scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (bounded : BitmapBudget scale s) : removeWork p s ≤ scale * stackWork p s := by
  have positive := bounded.positive
  cases p
  case seq a b =>
    have first := removeWork_scaled scale a s bounded
    have second := removeWork_scaled scale b _ (bounded.evaluated a)
    rw [removeWork, stackWork]
    simp only [Nat.mul_add] at *
    omega
  case ite cmp reg ri a b =>
    have first := removeWork_scaled scale a s bounded
    have second := removeWork_scaled scale b s bounded
    rw [removeWork, stackWork]
    simp only [Nat.mul_add] at *
    omega
  case loop body =>
    have first := removeWork_scaled scale body s bounded
    rw [removeWork, stackWork]
    split_ifs with continuing
    · have rest := removeWork_scaled scale (.loop body) _ ((bounded.evaluated body).decClock)
      simp only [Nat.mul_add] at *
      omega
    · simp only [Nat.mul_add, Nat.add_zero] at *
      omega
  case storeConsts a b c =>
    rw [removeWork, stackWork] <;> first | simpa only [Nat.mul_comm] using bounded.leaf | simp
  case jumpLower a b dest =>
    rw [removeWork, stackWork]
    split_ifs with zero
    · omega
    · split <;> simp_all only
      · omega
      · rename_i body found
        have child := removeWork_scaled scale body (decClock s) bounded.decClock
        simp only [Nat.mul_add] at *
        omega
  case rawCall dest =>
    rw [removeWork, stackWork]
    split_ifs with zero
    · omega
    · split <;> simp_all only
      · rename_i body found
        have child := removeWork_scaled scale body (decClock s) bounded.decClock
        simp only [Nat.mul_add] at *
        omega
      · omega
  case call ret dest handler =>
    rcases ret with _ | ⟨rp,link,l1,l2⟩
    · rw [removeWork, stackWork]
      split_ifs with zero
      · omega
      · split <;> simp_all only
        · omega
        · rename_i body found
          have child := removeWork_scaled scale body (decClock s) bounded.decClock
          simp only [Nat.mul_add] at *
          omega
    · rw [removeWork, stackWork]
      split_ifs with zero
      · omega
      · split <;> simp_all only
        · omega
        · rename_i body found
          have entry := (bounded.setVar link (.loc l1 l2)).decClock
          have first := removeWork_scaled scale body _ entry
          have next := entry.evaluated body
          have second := removeWork_scaled scale rp _ next
          cases handler with
          | none =>
            simp only [Nat.add_zero, Nat.mul_add, Nat.mul_left_comm scale 2] at *
            omega
          | some handler =>
            rcases handler with ⟨hp,hl1,hl2⟩
            have third := removeWork_scaled scale hp _ next
            simp only [Nat.mul_add, Nat.mul_left_comm scale 2] at *
            omega
  all_goals rw [removeWork, stackWork] <;> first | omega | simp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals try dsimp +zetaDelta at *
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock, setVar, fixClock]
  all_goals omega

/-- A concrete initial bitmap table supplies its own scale; only the empty
oracle invariant is needed to keep that scale fixed during recursion. -/
theorem BitmapBudget.of_emptyOracle {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (oracle : EmptyBitmapOracle s) :
    BitmapBudget (1 + (2 ^ width + 1) * s.bitmaps.length) s := by
  constructor
  · exact oracle
  · omega

/-- A uniform finite removal-work ceiling follows from fixed code and bitmap
bounds. This conservative ceiling remains geometric in the source fuel. -/
theorem removeWork_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (code : CodeSizeState limit s)
    (bitmap : BitmapBudget scale s) :
    removeWork p s ≤ scale * workCeiling limit s.clock (sizeOf p) := by
  exact Nat.le_trans (removeWork_scaled scale p s bitmap)
    (Nat.mul_le_mul_left scale (stackWork_ceiling limit p s small code))

#print axioms removeWork_ceiling
#print axioms BitmapBudget.of_emptyOracle
#print axioms removeWork_scaled
end InitECandidate.Runtime.StackRemove
