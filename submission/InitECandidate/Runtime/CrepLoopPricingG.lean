import InitECandidate.Runtime.LoopBoundedG
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! A Loop pricing of Crep work at any leaf price: a code allowance, a value
price for the residual Loop expression of compiled Crep expressions, and the
leaf facts the compiled non-recursive Crep statements need. -/

structure LoopPricingG where
  L : LeafPrice
  A : CodeAllowance L
  /-- Price of a residual Loop value when assigned. -/
  vp : HolLoopExp 64 → Nat
  vps : List (HolLoopExp 64) → Nat
  vps_nil : vps [] = 0
  vps_cons : ∀ v vs, vps (v :: vs) = vp v + vps vs
  price : CrepExpHOL 64 → Nat
  priceList : List (CrepExpHOL 64) → Nat
  exprOk : ∀ (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (e : CrepExpHOL 64),
    ∃ cost, A.works (compileExpHOLExact context tmp live e).1 = some cost ∧
      cost + vp (compileExpHOLExact context tmp live e).2.1 ≤ price e
  listOk : ∀ (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (es : List (CrepExpHOL 64)),
    ∃ cost, A.works (compileExpsHOLExact context tmp live es).1 = some cost ∧
      cost + vps (compileExpsHOLExact context tmp live es).2.1 ≤ priceList es
  /-- Generated assignments are within the value price. -/
  assignWork : ∀ n v, ∃ k, A.work (.assign n v) = some k ∧ k ≤ vp v
  /-- Leaf prices of the Loop statements compiled Crep leaves end in. -/
  assignOk : ∀ n v, ∃ k, L.lf (.assign n v) = some k ∧ k ≤ vp v
  tickC : Nat
  tickOk : ∃ k, L.lf .tick = some k ∧ k ≤ tickC
  breakC : Nat
  breakOk : ∀ l, ∃ k, L.lf (.break l) = some k ∧ k ≤ breakC
  contC : Nat
  contOk : ∀ l, ∃ k, L.lf (.continue l) = some k ∧ k ≤ contC
  raiseC : Nat
  raiseOk : ∀ e, ∃ k, L.lf (.raise e) = some k ∧ k ≤ raiseC
  returnC : Nat
  returnOk : ∀ vs, ∃ k, L.lf (.return vs) = some k ∧ k ≤ returnC
  setC : Nat
  setOk : ∀ a v, ∃ k, L.lf (.setGlobal a v) = some k ∧ k ≤ vp v + setC
  shareC : Nat
  shareOk : ∀ op n v, ∃ k, L.lf (.shMem op n v) = some k ∧ k ≤ vp v + shareC
  storeC : Nat
  storeOk : ∀ e v, ∃ k, L.lf (.store e v) = some k ∧ k ≤ vp e + storeC
  store32C : Nat
  store32Ok : ∀ a v, ∃ k, L.lf (.store32 a v) = some k ∧ k ≤ store32C
  storeByteOk : ∀ a v, ∃ k, L.lf (.storeByte a v) = some k ∧ k ≤ store32C
  ffiC : Nat
  ffiOk : ∀ f a b d e live, ∃ k, L.lf (.ffi f a b d e live) = some k ∧ k ≤ ffiC
  primC : Nat
  primOk : ∀ ds op as, ∃ k, L.lf (.primitive ds op as) = some k ∧ k ≤ primC

namespace LoopPricingG
variable (P : LoopPricingG)

/-- Static price of the non-recursive Crep statements. -/
def leafPrice : CrepProgHOL 64 → Option Nat
  | .skip => some 0
  | .tick => some P.tickC
  | .break _ => some P.breakC
  | .continue _ => some P.contC
  | .extCall _ _ _ _ _ => some P.ffiC
  | .raise _ => some (P.vp (.const 0) + P.raiseC)
  | .assign _ value => some (P.price value)
  | .storeGlob _ value => some (P.price value + P.setC)
  | .shMem _ _ address => some (P.price address + P.shareC)
  | .store address value => some (P.price address + P.price value + P.storeC)
  | .store32 address value | .storeByte address value =>
      some (P.price address + P.price value + P.store32C)
  | .return values => some (P.priceList values + P.returnC)
  | .primitive _ _ _ => some P.primC
  | _ => none

theorem assign_codes (names : List Nat) (values : List (HolLoopExp 64)) :
    ∃ cost, P.A.works (names.zipWith HolLoopProg.assign values) = some cost ∧ cost ≤ P.vps values := by
  induction names generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, CodeAllowance.works], Nat.zero_le _⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, CodeAllowance.works], Nat.zero_le _⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      obtain ⟨k, hk, hle⟩ := P.assignWork name value
      refine ⟨k + cost, ?_, ?_⟩
      · simp [List.zipWith, CodeAllowance.works, hk, supported]
      · rw [P.vps_cons]; omega

end LoopPricingG

#print axioms LoopPricingG.assign_codes
end InitECandidate.Runtime.FineCost
