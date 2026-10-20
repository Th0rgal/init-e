import InitECandidate.Runtime.PtUBWritersGD
/-!
Registry writes in the builder world: the registry with region survives writes to outside non-cell words
(`regTR_frameS`), the actual `htab_set` call statement on a registry table other than the content table re-establishes
it with the region grown by fresh heap (`aqgd_call_regSetJ`), and both are world steps (`ust_of_rp`, `ust_of_sk`,
`aqgd_call_regSetW`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section rf
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
  {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} {Rr : BitVec 64 → Prop}

/-- Writes confined to outside words that are no pointer cell keep the registry with region. -/
theorem regTR_frameS (h : RegTR n c T Out H M D B ko Rr) (S : BitVec 64 → Prop)
    (hS : ∀ x, S x → Out x ∧ ∀ i, x ≠ c i) (keep : ∀ x, ¬ S x → M' x = M x) : RegTR n c T Out H M' D B ko Rr := by
  obtain ⟨l,pure,mem,tc,ab,rr⟩ := h
  have rt := regT_frame (D := D) (B := B) ⟨l,pure,mem,tc,ab⟩ S hS keep
  obtain ⟨l2,pure2,mem2,tc2,ab2⟩ := rt
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  exact ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x (fun hs => by
      rcases hx with rfl | hx
      · exact (hS _ hs).2 i rfl
      · exact pure.2.2 x (hS x hs).1 i (Or.inl hx))),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x (fun hs => pure.2.2 x (hS x hs).1 ko (intabf_canon hx))),ab,rr⟩

#print axioms regTR_frameS
end rf

section rs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Rr : BitVec 64 → Prop}
  {Nj H0 : BitVec 64} {M0 : Mem} {G1 : GA}

/-- The actual `htab_set(et, ek, ev)` call statement on registry table `kd ≠ ko` over the registry with region. -/
theorem aqgd_call_regSetJ {LP : GA → Prop} {kd : Fin n} (ne : kd ≠ ko) (et ek ev : ExpHOL 64) (K V : BitVec 64)
    (reg : RegTR n c T Out H0 M0 D B ko Rr) (hH : HeapIs G1 H0)
    (hn : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (p0 : P0.toNat ≤ H0.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M0 → s.globals = G1 → LP s.locals →
      ∀ vs, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] = some vs →
        vs = [.val (.word (T kd)),.val (.word K),.val (.word V)]) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False) (fun L M G => LP L ∧ M = M0 ∧ G = G1)
      (fun L M G => LP L ∧ RPPost n c T Out D B ko Rr H0 Nj M0 M G) RR
      (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) := by
  obtain ⟨l,pure,mem,tc,ab,rr⟩ := reg
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => LK (irP0 (T kd) K V) L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost (T kd) ((l kd).canon (T kd) H0) M0' (l kd).C (l kd).SD
        (l kd).KS (l kd).VS (l kd).US (l kd).OS (l kd).OPS H0 M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    have hH' : HeapIs G0' H0 := by rw [hG]; exact hH
    have hn' : G0'.lookup (ofString "journal_n") = some (.val (.word Nj)) := by rw [hG]; exact hn
    have mem' : RegMem n c T l M0' := by rw [hM]; exact mem
    have lay := (pure.1 kd).1
    have hwk : ¬ (l kd).canon (T kd) H0 w := fun hc => by
      rcases hc with h | h | h
      · exact hwR (rr kd w (Or.inr (Or.inl h)))
      · exact hwR (rr kd w (Or.inr (Or.inr h)))
      · omega
    exact aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_rebound (set_aqmh (P0 := H0) (T kd) K V _ (l kd).KL (l kd).SD (l kd).C (l kd).N (l kd).KS
        (l kd).VS (l kd).US (l kd).OS (l kd).OPS (l kd).b lay M0' hwk H0 (le_refl _)) p0)))
      (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide)))
      (fun L M G ⟨hk,hM,hG⟩ => by rw [hM,hG]; exact ⟨hn',H0,hH',le_refl _,hk,(mem' kd).2,rfl,rfl⟩)
      (fun _ _ _ _ => trivial) (fun v M' G' ⟨hn',H',hH',post⟩ => ⟨hn',H',hH',post⟩)
  · intro F s values callee rs _ G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    have := hargs s hM hG1 lp values args
    subst this
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨hn',H',hH',post⟩
    subst hM hG
    obtain ⟨reg',le,frX⟩ := regTR_set ne l pure mem tc ab rr post
    exact ⟨lp,H',hH',le,reg',hn',frX⟩

#print axioms aqgd_call_regSetJ
end rs

section ws
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop}
  {M1 : Mem} {G1 : GA}

/-- A registry-table set is a world step. -/
theorem ust_of_rp (wsf : WsIFrame WsI) {M : Mem} {G : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 G1)
    (rp : RPPost n c T Out D B ko Rr H Nj M1 M G) (bg : BalG BA IA IS KB Ix G) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G := by
  obtain ⟨_,_,_,bw,_,wi,rB,dRO,dis,hsk⟩ := u
  obtain ⟨H',hH',le,reg',hn,fr⟩ := rp
  have oB := wsf.2 M1 H Ow wi
  have bB := bw.2.2
  refine ⟨ADs,Rg,H',fun x => Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat),Ow,⟨hH',hn,bg,
    balW_mono (balW_frame bw (fun k hk x hx => fr x (bB k hk x hx) (dis k hk x hx).1)) le,reg',
    wsf.1 M1 H Ow M H' wi (fun x hx => fr x (oB x hx) (fun h => dRO x hx h)) le,fun x hx => ?_,fun x ho hr => ?_,
    fun k hk x hx => ⟨fun hr => ?_,(dis k hk x hx).2⟩,fun x h => Or.inl (hsk x h)⟩,le,fun _ h => h,
    fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x hx => hx,fun x h => Or.inl h,fun x hx _ hr _ => fr x hx hr⟩
  · rcases hx with h | ⟨_,h⟩
    · have := rB x h; omega
    · exact h
  · rcases hr with h | ⟨a1,_⟩
    · exact dRO x ho h
    · have := oB x ho; omega
  · have := bB k hk x hx
    rcases hr with h | ⟨a1,_⟩
    · exact (dis k hk x hx).1 h
    · omega

#print axioms ust_of_rp

/-- Writes inside the scratch region (outside non-cell words), globals kept, are a world step. -/
theorem ust_of_sk (wsf : WsIFrame WsI) {M : Mem} {G : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 G1) (S : BitVec 64 → Prop)
    (hin : ∀ x, S x → Sk x) (hS : ∀ x, S x → Out x ∧ ∀ i, x ≠ c i) (fr : ∀ x, ¬ S x → M x = M1 x) (hG : G = G1) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G := by
  subst hG
  obtain ⟨hH,hn,bg,bw,reg,wi,rB,dRO,dis,hsk⟩ := u
  refine ⟨ADs,Rg,H,Rr,Ow,⟨hH,hn,bg,balW_frame bw (fun k hk x hx => fr x (fun hs => (dis k hk x hx).1 (hsk x (hin x hs)))),
    regTR_frameS reg S hS fr,
    wsf.1 M1 H Ow M H wi (fun x hx => fr x (fun hs => dRO x hx (hsk x (hin x hs)))) (le_refl _),rB,dRO,dis,hsk⟩,
    le_refl _,fun _ h => h,fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x h => Or.inl h,fun x h => Or.inl h,
    fun x _ _ hr _ => fr x (fun hs => hr (hsk x (hin x hs)))⟩

#print axioms ust_of_sk
end ws
end InitECandidate.Runtime
