import InitECandidate.Runtime.CrepWorkF
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Indexed Crep work is monotone in every price: work at pointwise smaller
prices exists, of no larger total. -/

section
variable {price price' : CrepExpHOL 64 → Nat} {priceList priceList' : List (CrepExpHOL 64) → Nat}
  {unit unit' prim prim' shortP shortP' ret ret' : Nat} {callP callP' : CName → CName → Nat → Nat}

theorem CrepWorkF.mono {σ : Type} {fn : CName} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (hp : ∀ e, price' e ≤ price e) (hl : ∀ es, priceList' es ≤ priceList es)
    (hu : unit' ≤ unit) (hm : prim' ≤ prim) (hc : ∀ f g n, callP' f g n ≤ callP f g n)
    (hs : shortP' ≤ shortP) (hr : ret' ≤ ret)
    (work : CrepWorkF price priceList unit prim callP shortP ret fn t p w) :
    ∃ w', CrepWorkF price' priceList' unit' prim' callP' shortP' ret' fn t p w' ∧ w' ≤ w := by
  induction work with
  | skip fn t => exact ⟨_, .skip fn t, Nat.le_refl _⟩
  | tick fn t => exact ⟨_, .tick fn t, hu⟩
  | breakStmt fn t l => exact ⟨_, .breakStmt fn t l, hu⟩
  | continueStmt fn t l => exact ⟨_, .continueStmt fn t l, hu⟩
  | raise fn t c => exact ⟨_, .raise fn t c, by omega⟩
  | assign fn t n v => exact ⟨_, .assign fn t n v, hp v⟩
  | storeGlob fn t a v => exact ⟨_, .storeGlob fn t a v, by have := hp v; omega⟩
  | store fn t a v => exact ⟨_, .store fn t a v, by have := hp a; have := hp v; omega⟩
  | store32 fn t a v => exact ⟨_, .store32 fn t a v, by have := hp a; have := hp v; omega⟩
  | storeByte fn t a v => exact ⟨_, .storeByte fn t a v, by have := hp a; have := hp v; omega⟩
  | returnStmt fn t vs => exact ⟨_, .returnStmt fn t vs, by have := hl vs; omega⟩
  | primitive fn t ns op as => exact ⟨_, .primitive fn t ns op as, by omega⟩
  | shMem fn t op n a => exact ⟨_, .shMem fn t op n a, by have := hp a; omega⟩
  | extCall fn t f a b c d => exact ⟨_, .extCall fn t f a b c d, hu⟩
  | @decFailure fn t name value body failed => exact ⟨_, .decFailure failed, hp value⟩
  | @dec fn t name value body word bodyWork evaluated _ ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    exact ⟨_, .dec evaluated k1, by have := hp value; omega⟩
  | seqNext _ run _ ih1 ih2 =>
    obtain ⟨w1, k1, b1⟩ := ih1; obtain ⟨w2, k2, b2⟩ := ih2
    exact ⟨_, .seqNext k1 run k2, by omega⟩
  | seqStop _ run ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    exact ⟨_, .seqStop k1 run, b1⟩
  | @iteBranch fn t condition yes no word branchWork guard _ ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    exact ⟨_, .iteBranch guard k1, by have := hp condition; omega⟩
  | @iteInvalid fn t condition yes no invalid =>
    exact ⟨_, .iteInvalid invalid, by have := hp condition; omega⟩
  | @whileExit fn t condition body exit =>
    exact ⟨_, .whileExit exit, by have := hp condition; omega⟩
  | @whileTimeout fn t condition body word guard nonzero clock =>
    exact ⟨_, .whileTimeout guard nonzero clock, by have := hp condition; omega⟩
  | @whileLoop fn t condition body word bodyWork result middle restWork guard nonzero clock _ run again _ ih1 ih2 =>
    obtain ⟨w1, k1, b1⟩ := ih1; obtain ⟨w2, k2, b2⟩ := ih2
    exact ⟨_, .whileLoop guard nonzero clock k1 run again k2, by have := hp condition; omega⟩
  | @whileStop fn t condition body word bodyWork result middle guard nonzero clock _ run stop ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    exact ⟨_, .whileStop guard nonzero clock k1 run stop, by have := hp condition; omega⟩
  | @callShort fn t returnInfo function arguments short =>
    exact ⟨_, .callShort short, by have := hc fn function (crepRetCount returnInfo); have := hl arguments; omega⟩
  | @callBody fn t returnInfo function arguments values body locals bodyWork result post args lookup names clock
      _ run unhandled ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    refine ⟨_, .callBody args lookup names clock k1 run unhandled, ?_⟩
    have := hc fn function (crepRetCount returnInfo); have := hl arguments
    have := Nat.mul_le_mul_right (crepCallPayloadWords result) hr
    omega
  | @callHandler fn t rts code handler function arguments values body locals bodyWork post handlerWork args lookup
      names clock _ run _ ih1 ih2 =>
    obtain ⟨w1, k1, b1⟩ := ih1; obtain ⟨w2, k2, b2⟩ := ih2
    exact ⟨_, .callHandler args lookup names clock k1 run k2, by
      have := hc fn function rts.length; have := hl arguments; omega⟩

end

#print axioms CrepWorkF.mono
end InitECandidate.Runtime.FineCost
