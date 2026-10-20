import InitECandidate.Runtime.PtStorRemoveGD
import InitECandidate.Runtime.DigitsDivmodGD
/-!
Call statements of the actual block-access-list writers (`add_balance_change`, `add_nonce_change`,
`add_code_change`, `add_storage_write`, `bal_remove_change`, `remove_storage_write`): the caller's locals are kept and
the block-access-list state steps from the call entry (`BalStep`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gen
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A call statement from a body spec whose return post `X` only mentions memory and globals. -/
theorem aqgd_call_post {LP : GA → Prop} {X : Mem → GA → Prop} (f : MlS) (args : List (ExpHOL 64))
    (ps : List (MlS × ShapeHOL)) (body : ProgHOL 64) (rs : ShapeHOL)
    (installed : originalRuntimeCode.lookup f = some (ps,body,rs)) (LPe : GA → Prop) (M1 : Mem) (G1 : GA)
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPe L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun _ M G => X M G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs', s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs') → LPe callee) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1) (fun L M G => LP L ∧ X M G) RR
      (.call (some (none,none)) f args) := by
  refine aqgd_callSpecS (Vn' := fun _ => False) (Pe := fun _ M0' G0' L M G => LPe L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ _ M' G' => X M' G') f args ps body rs installed (fun _ _ _ _ _ h => h.elim) ?_ ?_ ?_
  · intro L0 M0 G0 ⟨_,hM,hG⟩
    subst hM hG
    exact aqgd_conseq hb (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)
  · intro F s values callee rs' _ H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    exact ⟨hpe s values callee rs' hM hG1 lp args lookup,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ x
    exact ⟨lp,x⟩

#print axioms aqgd_call_post
end gen

section bw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `add_balance_change` call statement. -/
theorem aqgd_call_addBalance (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A I b0 b1 b2 b3 : BitVec 64) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea ei eb : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,eb] =
        some [.val (.word A),.val (.word I),.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "add_balance_change") [ea,ei,eb]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_addBalanceChange_lookup _ M1 G1
    (aqgd_conseq (addBalance_aqgd bk BA IA IS KB Ix A I b0 b1 b2 b3 ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_addBalanceChange_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

/-- The actual `add_nonce_change` call statement. -/
theorem aqgd_call_addNonce (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A I Nn : BitVec 64) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea ei en : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,en] =
        some [.val (.word A),.val (.word I),.val (.word Nn)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "add_nonce_change") [ea,ei,en]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_addNonceChange_lookup _ M1 G1
    (aqgd_conseq (addNonce_aqgd bk BA IA IS KB Ix A I Nn ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_addNonceChange_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

/-- The actual `add_code_change` call statement. -/
theorem aqgd_call_addCode (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A I Cd Cl : BitVec 64) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea ei ec el : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,ec,el] =
        some [.val (.word A),.val (.word I),.val (.word Cd),.val (.word Cl)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "add_code_change") [ea,ei,ec,el]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_addCodeChange_lookup _ M1 G1
    (aqgd_conseq (addCode_aqgd bk BA IA IS KB Ix A I Cd Cl ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_addCodeChange_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

/-- The actual `add_storage_write` call statement. -/
theorem aqgd_call_addStorage (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A Sl I v0 v1 v2 v3 : BitVec 64) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea es ei ev : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,es,ei,ev] =
        some [.val (.word A),.val (.word Sl),.val (.word I),.rStruct [.val (.word v0),.val (.word v1),.val (.word v2),.val (.word v3)]]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "add_storage_write") [ea,es,ei,ev]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_addStorageWrite_lookup _ M1 G1
    (aqgd_conseq (addStorage_aqgd bk BA IA IS KB Ix A Sl I v0 v1 v2 v3 ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hwP p0 hK hKE hS hSE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_addStorageWrite_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

/-- The actual `bal_remove_change` call statement. -/
theorem aqgd_call_removeChange (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A Wc E I : BitVec 64) (sel : ChgSel Wc E)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea ew ee ei : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ew,ee,ei] =
        some [.val (.word A),.val (.word Wc),.val (.word E),.val (.word I)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "bal_remove_change") [ea,ew,ee,ei]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_balRemoveChange_lookup _ M1 G1
    (aqgd_conseq (removeChange_aqgd bk BA IA IS KB Ix A Wc E I ADs Rg H Nj M1 G1 sel bw hH1 hn1 hB1 hwR hK hKE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_balRemoveChange_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

/-- The actual `remove_storage_write` call statement. -/
theorem aqgd_call_removeStorage (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H Nj : BitVec 64) (M1 : Mem) (G1 : GA)
    (bw : BalW D B BA IA IS KB ADs Rg H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hB1 : BalG BA IA IS KB Ix G1)
    (hwR : ∀ c, BalK.live ADs c → ¬ Rg c w)
    (A Sl I : BitVec 64)
    (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) {LP : GA → Prop} (ea es ei : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,es,ei] =
        some [.val (.word A),.val (.word Sl),.val (.word I)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "remove_storage_write") [ea,es,ei]) := by
  refine aqgd_call_post _ _ _ _ _ originalRuntimeCode_removeStorageWrite_lookup _ M1 G1
    (aqgd_conseq (removeStorage_aqgd bk BA IA IS KB Ix A Sl I ADs Rg H Nj M1 G1 bw hH1 hn1 hB1 hwR hK hKE hS hSE Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.2)) ?_
  intro F s values callee rs' hM hG lp args lookup
  rw [hargs s hM hG lp] at args
  simp only [Option.some.injEq] at args
  subst args
  have e := callee_eq originalRuntimeCode_removeStorageWrite_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩

#print axioms aqgd_call_addBalance
#print axioms aqgd_call_addNonce
#print axioms aqgd_call_addCode
#print axioms aqgd_call_addStorage
#print axioms aqgd_call_removeChange
#print axioms aqgd_call_removeStorage
end bw
section tr
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB : BitVec 64}

/-- Two block-access-list steps compose. -/
theorem balStep_trans {ADs ADs' : Set (BitVec 64)} {Rg Rg' : BalK → BitVec 64 → Prop} {H H' Nj : BitVec 64}
    {M1 M2 M3 : Mem} {G3 : GA} (le : H.toNat ≤ H'.toNat) (sub : ADs ⊆ ADs')
    (gr : ∀ c, BalK.live ADs' c → ∀ x, Rg' c x → (BalK.live ADs c ∧ Rg c x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (fr : ∀ x, x.toNat < H.toNat → (∀ c, BalK.live ADs c → ¬ Rg c x) → M2 x = M1 x)
    (s2 : BalStep D B BA IA IS KB ADs' Rg' H' Nj M2 M3 G3) : BalStep D B BA IA IS KB ADs Rg H Nj M1 M3 G3 := by
  obtain ⟨ADs'',Rg'',H'',hH3,le2,hn3,bw3,sub2,gr2,fr2⟩ := s2
  refine ⟨ADs'',Rg'',H'',hH3,by omega,hn3,bw3,fun x h => sub2 (sub h),fun c hc x hx => ?_,fun x hx hn => ?_⟩
  · rcases gr2 c hc x hx with ⟨l1,h1⟩ | ⟨a1,b1⟩
    · rcases gr c l1 x h1 with h | ⟨a2,b2⟩
      · exact Or.inl h
      · exact Or.inr ⟨a2,by omega⟩
    · exact Or.inr ⟨by omega,b1⟩
  · refine (fr2 x (by omega) (fun c hc h => ?_)).trans (fr x hx hn)
    rcases gr c hc x h with ⟨l1,h1⟩ | ⟨a1,_⟩
    · exact hn c l1 h1
    · omega

#print axioms balStep_trans
end tr
end InitECandidate.Runtime
