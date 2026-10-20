import InitECandidate.Runtime.PtGetPreStorGD
/-!
The block-access-list builder world `UW`: heap pointer, journal counter, block-access-list globals, the block-access-list
objects (`BalW`), the registry with owned region (`RegTR`) and the witness invariant (`WsI`), with the three regions
pairwise disjoint and below the heap. `USt`: a step of the world from an entry memory (objects may be added, regions
grow only by fresh heap, memory below the entry heap outside all regions unchanged). Block-access-list writer steps
(`BalStep`) and pre-state reads (`GPPost`) are world steps.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The builder world. -/
def UW (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB Ix : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (Nj : BitVec 64)
    (ADs : Set (BitVec 64)) (Rg : BalK → BitVec 64 → Prop) (H : BitVec 64) (Rr Ow : BitVec 64 → Prop)
    (M : Mem) (G : GA) : Prop :=
  HeapIs G H ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G ∧
    BalW D B BA IA IS KB ADs Rg H M ∧ RegTR n c T Out H M D B ko Rr ∧ WsI M H Ow ∧
    (∀ x, Rr x → x.toNat < H.toNat) ∧ (∀ x, Ow x → ¬ Rr x) ∧
    ∀ k, BalK.live ADs k → ∀ x, Rg k x → ¬ Rr x ∧ ¬ Ow x

/-- A step of the builder world from entry memory `M1`. -/
def USt (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB Ix : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (Nj : BitVec 64)
    (ADs : Set (BitVec 64)) (Rg : BalK → BitVec 64 → Prop) (H : BitVec 64) (Rr Ow : BitVec 64 → Prop)
    (M1 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ (ADs' : Set (BitVec 64)) (Rg' : BalK → BitVec 64 → Prop) (H' : BitVec 64) (Rr' Ow' : BitVec 64 → Prop),
    UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs' Rg' H' Rr' Ow' M G ∧ H.toNat ≤ H'.toNat ∧ ADs ⊆ ADs' ∧
    (∀ k, BalK.live ADs' k → ∀ x, Rg' k x → (BalK.live ADs k ∧ Rg k x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    (∀ x, Rr' x → Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    (∀ x, Ow' x → Ow x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    ∀ x, x.toNat < H.toNat → (∀ k, BalK.live ADs k → ¬ Rg k x) → ¬ Rr x → ¬ Ow x → M x = M1 x

section uw
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Nj : BitVec 64}
  {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop}
  {M1 : Mem} {G1 : GA}

theorem ust_refl (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M1 G1 :=
  ⟨ADs,Rg,H,Rr,Ow,u,le_refl _,fun _ h => h,fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x h => Or.inl h,fun x h => Or.inl h,
    fun _ _ _ _ _ => rfl⟩

theorem ust_trans {ADs' : Set (BitVec 64)} {Rg' : BalK → BitVec 64 → Prop} {H' : BitVec 64}
    {Rr' Ow' : BitVec 64 → Prop} {M2 M3 : Mem} {G3 : GA} (le : H.toNat ≤ H'.toNat) (sub : ADs ⊆ ADs')
    (gr : ∀ k, BalK.live ADs' k → ∀ x, Rg' k x → (BalK.live ADs k ∧ Rg k x) ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (grR : ∀ x, Rr' x → Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (grO : ∀ x, Ow' x → Ow x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))
    (fr : ∀ x, x.toNat < H.toNat → (∀ k, BalK.live ADs k → ¬ Rg k x) → ¬ Rr x → ¬ Ow x → M2 x = M1 x)
    (s2 : USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs' Rg' H' Rr' Ow' M2 M3 G3) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M3 G3 := by
  obtain ⟨A2,R2,H2,Rr2,Ow2,u,le2,sub2,gr2,grR2,grO2,fr2⟩ := s2
  refine ⟨A2,R2,H2,Rr2,Ow2,u,by omega,fun x h => sub2 (sub h),fun k hk x hx => ?_,fun x hx => ?_,fun x hx => ?_,
    fun x hx hn hr ho => ?_⟩
  · rcases gr2 k hk x hx with ⟨l1,h1⟩ | ⟨a1,b1⟩
    · rcases gr k l1 x h1 with h | ⟨a2,b2⟩
      · exact Or.inl h
      · exact Or.inr ⟨a2,by omega⟩
    · exact Or.inr ⟨by omega,b1⟩
  · rcases grR2 x hx with h | ⟨a1,b1⟩
    · rcases grR x h with h | ⟨a2,b2⟩
      · exact Or.inl h
      · exact Or.inr ⟨a2,by omega⟩
    · exact Or.inr ⟨by omega,b1⟩
  · rcases grO2 x hx with h | ⟨a1,b1⟩
    · rcases grO x h with h | ⟨a2,b2⟩
      · exact Or.inl h
      · exact Or.inr ⟨a2,by omega⟩
    · exact Or.inr ⟨by omega,b1⟩
  · refine (fr2 x (by omega) (fun k hk h => ?_) (fun h => ?_) (fun h => ?_)).trans (fr x hx hn hr ho)
    · rcases gr k hk x h with ⟨l1,h1⟩ | ⟨a1,_⟩
      · exact hn k l1 h1
      · omega
    · rcases grR x h with h | ⟨a1,_⟩
      · exact hr h
      · omega
    · rcases grO x h with h | ⟨a1,_⟩
      · exact ho h
      · omega

#print axioms ust_trans

theorem balW_frame {M : Mem} (bw : BalW D B BA IA IS KB ADs Rg H M1)
    (keep : ∀ k, BalK.live ADs k → ∀ x, Rg k x → M x = M1 x) : BalW D B BA IA IS KB ADs Rg H M :=
  ⟨fun k hk => balV_frame k (bw.1 k hk) (keep k hk),bw.2.1,bw.2.2⟩

theorem balW_mono {H' : BitVec 64} (bw : BalW D B BA IA IS KB ADs Rg H M1) (le : H.toNat ≤ H'.toNat) :
    BalW D B BA IA IS KB ADs Rg H' M1 :=
  ⟨fun k hk => balV_mono k (bw.1 k hk) le,bw.2.1,fun k hk x hx => by have := bw.2.2 k hk x hx; omega⟩

/-- A block-access-list writer step (with the globals kept) is a world step. -/
theorem ust_of_balStep (wsf : WsIFrame WsI) {M : Mem} {G : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1)
    (bs : BalStep D B BA IA IS KB ADs Rg H Nj M1 M G) (bg : BalG BA IA IS KB Ix G) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G := by
  obtain ⟨_,_,_,_,reg,wi,rB,dRO,dis⟩ := u
  obtain ⟨ADs',Rg',H',hH',le,hn,bw',sub,gr,fr⟩ := bs
  have oB := wsf.2 M1 H Ow wi
  refine ⟨ADs',Rg',H',Rr,Ow,⟨hH',hn,bg,bw',
    regTR_mono (regTR_frame reg (fun x hx => fr x (rB x hx) (fun k hk hr => (dis k hk x hr).1 hx))) le,
    wsf.1 M1 H Ow M H' wi (fun x hx => fr x (oB x hx) (fun k hk hr => (dis k hk x hr).2 hx)) le,
    fun x hx => by have := rB x hx; omega,dRO,fun k hk x hx => ?_⟩,le,sub,gr,fun x h => Or.inl h,
    fun x h => Or.inl h,fun x hx hn _ _ => fr x hx hn⟩
  rcases gr k hk x hx with ⟨l1,h1⟩ | ⟨a1,_⟩
  · exact dis k l1 x h1
  · exact ⟨fun h => by have := rB x h; omega,fun h => by have := oB x h; omega⟩

#print axioms ust_of_balStep

/-- A pre-state read is a world step. -/
theorem ust_of_gp (wsf : WsIFrame WsI) {M : Mem} {G : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1)
    (gp : GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M1 M G) :
    USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G := by
  obtain ⟨_,_,_,bw,_,wi,rB,dRO,dis⟩ := u
  obtain ⟨H2,H',Ow',hH',le2,le',hn,bg,reg',wi',sub',fr⟩ := gp
  have oB := wsf.2 M1 H Ow wi
  have bB := bw.2.2
  refine ⟨ADs,Rg,H',fun x => Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H2.toNat),Ow',⟨hH',hn,bg,
    balW_mono (balW_frame bw (fun k hk x hx => fr x (bB k hk x hx) (dis k hk x hx).1 (dis k hk x hx).2)) (by omega),
    reg',wi',fun x hx => ?_,fun x ho hr => ?_,fun k hk x hx => ⟨fun hr => ?_,fun ho => ?_⟩⟩,by omega,fun _ h => h,
    fun k hk x hx => Or.inl ⟨hk,hx⟩,fun x hx => ?_,fun x hx => ?_,fun x hx hn hr ho => fr x hx hr ho⟩
  · rcases hx with h | ⟨_,h⟩
    · have := rB x h; omega
    · omega
  · rcases sub' x ho with h | ⟨a1,_⟩ <;> rcases hr with h' | ⟨_,b2⟩
    · exact dRO x h h'
    · have := oB x h; omega
    · have := rB x h'; omega
    · omega
  · have := bB k hk x hx
    rcases hr with h | ⟨a1,_⟩
    · exact (dis k hk x hx).1 h
    · omega
  · have := bB k hk x hx
    rcases sub' x ho with h | ⟨a1,_⟩
    · exact (dis k hk x hx).2 h
    · omega
  · rcases hx with h | ⟨a1,b1⟩
    · exact Or.inl h
    · exact Or.inr ⟨a1,by omega⟩
  · rcases sub' x hx with h | ⟨a1,b1⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega,b1⟩

#print axioms ust_of_gp
end uw
end InitECandidate.Runtime
