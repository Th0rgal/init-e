import InitECandidate.Runtime.PtUWGD
/-!
World steps of the block-access-list builder: the sequencing combinator `aqgd_ust` (a triple from every world state
gives a triple from any state reached by a world step), key-buffer writes (`ust_of_kb`), fresh-heap blocks
(`ust_of_fresh`), a component confined to its region and fresh heap (`ust_of_comp`, e.g. a set on an index table),
and the world-level `get_pre_tx_account` / `get_pre_tx_storage` declared calls.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ws
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Nj : BitVec 64}
  {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop}
  {M1 : Mem} {G1 : GA} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}

/-- Sequencing through world steps. -/
theorem aqgd_ust {LP LP' : GA → Prop} {X : ValueHOL 64 → Prop} {p : ProgHOL 64}
    (h : ∀ (ADs' : Set (BitVec 64)) (Rg' : BalK → BitVec 64 → Prop) (H' : BitVec 64) (Rr' Ow' : BitVec 64 → Prop)
      (M2 : Mem) (G2 : GA), UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs' Rg' H' Rr' Ow' M2 G2 →
      H.toNat ≤ H'.toNat → (∀ k, BalK.live ADs' k → ¬ Rg' k w) → ¬ Rr' w → ¬ Ow' w →
      AQGD D B A w Vn (fun L M G => LP L ∧ M = M2 ∧ G = G2)
        (fun L M G => LP' L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs' Rg' H' Rr' Ow' M2 M G)
        (fun v M G => X v ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs' Rg' H' Rr' Ow' M2 M G) p)
    (hw : w.toNat < H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwr : ¬ Rr w) (hwo : ¬ Ow w) :
    AQGD D B A w Vn (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G)
      (fun L M G => LP' L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G)
      (fun v M G => X v ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G) p := by
  refine aqgd_ghostR (fun M2 G2 st => ?_)
  obtain ⟨A2,R2,H2,Rr2,Ow2,u,le,sub,gr,grR,grO,fr⟩ := st
  refine aqgd_conseq (h A2 R2 H2 Rr2 Ow2 M2 G2 u le (fun k hk hr => ?_) (fun hr => ?_) (fun ho => ?_))
    (fun _ _ _ h => h) (fun L M G ⟨lp,s2⟩ => ⟨lp,ust_trans le sub gr grR grO fr s2⟩)
    (fun v M G ⟨x,s2⟩ => ⟨x,ust_trans le sub gr grR grO fr s2⟩)
  · rcases gr k hk w hr with ⟨l1,h1⟩ | ⟨a1,_⟩
    · exact hwk k l1 h1
    · omega
  · rcases grR w hr with h | ⟨a1,_⟩
    · exact hwr h
    · omega
  · rcases grO w ho with h | ⟨a1,_⟩
    · exact hwo h
    · omega

#print axioms aqgd_ust

/-- Writes inside the key buffer keep the world. -/
theorem ust_of_kb (wsf : WsIFrame WsI) {M : Mem} {G : GA} (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1)
    (Win : BitVec 64 → Prop) (hin : ∀ x, Win x → Rg .kb x) (fr : ∀ x, ¬ Win x → M x = M1 x) (hG : G = G1) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G := by
  subst hG
  obtain ⟨hH,hn,bg,bw,reg,wi,rB,dRO,dis⟩ := u
  have nW : ∀ k, BalK.live ADs k → k ≠ .kb → ∀ x, Rg k x → ¬ Win x := fun k hk ne x hx hw =>
    bw.2.1 k .kb hk trivial ne x hx (hin x hw)
  refine ⟨ADs,Rg,H,Rr,Ow,⟨hH,hn,bg,⟨fun k hk => ?_,bw.2.1,bw.2.2⟩,
    regTR_frame reg (fun x hx => fr x (fun hw => (dis .kb trivial x (hin x hw)).1 hx)),
    wsf.1 M1 H Ow M H wi (fun x hx => fr x (fun hw => (dis .kb trivial x (hin x hw)).2 hx)) (le_refl _),rB,dRO,dis⟩,le_refl _,fun _ h => h,fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x h => Or.inl h,
    fun x h => Or.inl h,fun x _ hn _ _ => fr x (fun hw => hn .kb trivial (hin x hw))⟩
  by_cases e : k = .kb
  · subst e; exact bw.1 .kb hk
  · exact balV_frame k (bw.1 k hk) (fun x hx => fr x (nW k hk e x hx))

#print axioms ust_of_kb

/-- Memory below the world heap unchanged, heap grown, globals kept: a world step (fresh-heap blocks). -/
theorem ust_of_fresh (wsf : WsIFrame WsI) {M : Mem} {G : GA} {H' : BitVec 64}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1) (le : H.toNat ≤ H'.toNat)
    (hH' : HeapIs G H') (hn : G.lookup (ofString "journal_n") = some (.val (.word Nj))) (bg : BalG BA IA IS KB Ix G)
    (fr : ∀ x, x.toNat < H.toNat → M x = M1 x) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G := by
  obtain ⟨_,_,_,bw,reg,wi,rB,dRO,dis⟩ := u
  have oB := wsf.2 M1 H Ow wi
  refine ⟨ADs,Rg,H',Rr,Ow,⟨hH',hn,bg,balW_mono (balW_frame bw (fun k hk x hx => fr x (bw.2.2 k hk x hx))) le,
    regTR_mono (regTR_frame reg (fun x hx => fr x (rB x hx))) le,
    wsf.1 M1 H Ow M H' wi (fun x hx => fr x (oB x hx)) le,fun x hx => by have := rB x hx; omega,dRO,dis⟩,le,
    fun _ h => h,fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x h => Or.inl h,fun x h => Or.inl h,
    fun x hx _ _ _ => fr x hx⟩

#print axioms ust_of_fresh

/-- A live component changed within its region and the fresh heap (everything else below the heap kept): a world
step. -/
theorem ust_of_comp (wsf : WsIFrame WsI) {M : Mem} {G : GA} {H' : BitVec 64} (k : BalK) (hk : BalK.live ADs k)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1) (le : H.toNat ≤ H'.toNat)
    (hH' : HeapIs G H') (hn : G.lookup (ofString "journal_n") = some (.val (.word Nj))) (bg : BalG BA IA IS KB Ix G)
    (new : BalV D B BA IA IS KB ADs k (fun x => Rg k x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) H' M)
    (fr : ∀ x, x.toNat < H.toNat → ¬ Rg k x → M x = M1 x) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G := by
  obtain ⟨_,_,_,bw,reg,wi,rB,dRO,dis⟩ := u
  have oB := wsf.2 M1 H Ow wi
  refine ⟨ADs,_,H',Rr,Ow,⟨hH',hn,bg,balW_upd k hk bw le new fr,
    regTR_mono (regTR_frame reg (fun x hx => fr x (rB x hx) (fun h => (dis k hk x h).1 hx))) le,
    wsf.1 M1 H Ow M H' wi (fun x hx => fr x (oB x hx) (fun h => (dis k hk x h).2 hx)) le,
    fun x hx => by have := rB x hx; omega,dRO,fun k' hk' x hx => ?_⟩,le,fun _ h => h,fun k' hk' x hx => ?_,
    fun x h => Or.inl h,fun x h => Or.inl h,fun x hx hn _ _ => fr x hx (hn k hk)⟩
  · rcases hx with h | ⟨_,a1,_⟩
    · exact dis k' hk' x h
    · exact ⟨fun h => by have := rB x h; omega,fun h => by have := oB x h; omega⟩
  · rcases hx with h | ⟨_,a1,b1⟩
    · exact Or.inl ⟨hk',h⟩
    · exact Or.inr ⟨a1,b1⟩

#print axioms ust_of_comp
end ws
end InitECandidate.Runtime
