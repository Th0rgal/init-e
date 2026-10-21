import InitECandidate.Runtime.CrepWorkF
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Indexed Crep work is monotone in every price: work at pointwise smaller
prices exists, of no larger total. -/

/-- Statement prices pointwise at most others. -/
structure StmtK.Le (A B : StmtK) : Prop where
  tick : A.tick ≤ B.tick
  brk : A.brk ≤ B.brk
  cont : A.cont ≤ B.cont
  ffi : A.ffi ≤ B.ffi
  raise : A.raise ≤ B.raise
  storeGlob : A.storeGlob ≤ B.storeGlob
  shMem : A.shMem ≤ B.shMem
  store : A.store ≤ B.store
  store32 : A.store32 ≤ B.store32
  ret : ∀ n, A.ret n ≤ B.ret n
  prim : ∀ a b, A.prim a b ≤ B.prim a b
  ite : A.ite ≤ B.ite
  wh : A.wh ≤ B.wh
  argP : ∀ n, A.argP n ≤ B.argP n
  retW : A.retW ≤ B.retW
  exnP : A.exnP ≤ B.exnP
  hdlP : A.hdlP ≤ B.hdlP

theorem StmtK.Le.exit {A B : StmtK} (h : StmtK.Le A B) (r : Option (CrepResultHOLExact 64)) : A.exit r ≤ B.exit r := by
  rcases r with _ | r
  · exact Nat.le_refl _
  · cases r <;> simp only [StmtK.exit] <;> first | exact Nat.le_refl _ | exact h.exnP | exact Nat.mul_le_mul_right _ h.retW

section
variable {price price' : CrepExpHOL 64 → Nat} {priceList priceList' : List (CrepExpHOL 64) → Nat}
  {K K' : StmtK} {shortP shortP' : Nat} {callP callP' : CName → CName → Nat → Nat}

theorem CrepWorkF.mono {σ : Type} {fn : CName} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (hp : ∀ e, price' e ≤ price e) (hl : ∀ es, priceList' es ≤ priceList es) (hk : StmtK.Le K' K)
    (hc : ∀ f g n, callP' f g n ≤ callP f g n) (hs : shortP' ≤ shortP)
    (work : CrepWorkF price priceList K callP shortP fn t p w) :
    ∃ w', CrepWorkF price' priceList' K' callP' shortP' fn t p w' ∧ w' ≤ w := by
  induction work with
  | skip fn t => exact ⟨_, .skip fn t, Nat.le_refl _⟩
  | tick fn t => exact ⟨_, .tick fn t, hk.tick⟩
  | breakStmt fn t l => exact ⟨_, .breakStmt fn t l, hk.brk⟩
  | continueStmt fn t l => exact ⟨_, .continueStmt fn t l, hk.cont⟩
  | raise fn t c => exact ⟨_, .raise fn t c, hk.raise⟩
  | assign fn t n v => exact ⟨_, .assign fn t n v, hp v⟩
  | storeGlob fn t a v => exact ⟨_, .storeGlob fn t a v, by have := hp v; have := hk.storeGlob; omega⟩
  | store fn t a v => exact ⟨_, .store fn t a v, by have := hp a; have := hp v; have := hk.store; omega⟩
  | store32 fn t a v => exact ⟨_, .store32 fn t a v, by have := hp a; have := hp v; have := hk.store32; omega⟩
  | storeByte fn t a v => exact ⟨_, .storeByte fn t a v, by have := hp a; have := hp v; have := hk.store32; omega⟩
  | returnStmt fn t vs => exact ⟨_, .returnStmt fn t vs, by have := hl vs; have := hk.ret vs.length; omega⟩
  | primitive fn t ns op as => exact ⟨_, .primitive fn t ns op as, hk.prim _ _⟩
  | shMem fn t op n a => exact ⟨_, .shMem fn t op n a, by have := hp a; have := hk.shMem; omega⟩
  | extCall fn t f a b c d => exact ⟨_, .extCall fn t f a b c d, hk.ffi⟩
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
    exact ⟨_, .iteBranch guard k1, by have := hp condition; have := hk.ite; omega⟩
  | @iteInvalid fn t condition yes no invalid =>
    exact ⟨_, .iteInvalid invalid, by have := hp condition; have := hk.ite; omega⟩
  | @whileExit fn t condition body exit =>
    exact ⟨_, .whileExit exit, by have := hp condition; have := hk.wh; omega⟩
  | @whileTimeout fn t condition body word guard nonzero clock =>
    exact ⟨_, .whileTimeout guard nonzero clock, by have := hp condition; have := hk.wh; omega⟩
  | @whileLoop fn t condition body word bodyWork result middle restWork guard nonzero clock _ run again _ ih1 ih2 =>
    obtain ⟨w1, k1, b1⟩ := ih1; obtain ⟨w2, k2, b2⟩ := ih2
    exact ⟨_, .whileLoop guard nonzero clock k1 run again k2, by have := hp condition; have := hk.wh; omega⟩
  | @whileStop fn t condition body word bodyWork result middle guard nonzero clock _ run stop ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    exact ⟨_, .whileStop guard nonzero clock k1 run stop, by have := hp condition; have := hk.wh; omega⟩
  | @callShort fn t returnInfo function arguments short =>
    exact ⟨_, .callShort short, by
      have := hc fn function (crepRetCount returnInfo); have := hl arguments; have := hk.argP arguments.length; omega⟩
  | @callBody fn t returnInfo function arguments values body locals bodyWork result post args lookup names clock
      _ run unhandled ih =>
    obtain ⟨w1, k1, b1⟩ := ih
    refine ⟨_, .callBody args lookup names clock k1 run unhandled, ?_⟩
    have := hc fn function (crepRetCount returnInfo); have := hl arguments; have := hk.argP arguments.length
    have := hk.exit result
    omega
  | @callHandler fn t rts code handler function arguments values body locals bodyWork post handlerWork args lookup
      names clock _ run _ ih1 ih2 =>
    obtain ⟨w1, k1, b1⟩ := ih1; obtain ⟨w2, k2, b2⟩ := ih2
    exact ⟨_, .callHandler args lookup names clock k1 run k2, by
      have := hc fn function rts.length; have := hl arguments; have := hk.argP arguments.length; have := hk.hdlP; omega⟩

end

#print axioms CrepWorkF.mono
end InitECandidate.Runtime.FineCost
