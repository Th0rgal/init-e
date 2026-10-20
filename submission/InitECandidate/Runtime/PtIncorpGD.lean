import InitECandidate.Runtime.PtUBMainGD
/-!
Composition of `incorporate_tx_into_block` = `update_builder_from_tx(); merge_tx_into_block(); return 0`: the block
objects of the merge (the block outer map `bs + 32` and the merge target family) lie outside every region of the
block-access-list builder world, so they survive the builder; the builder world lies outside the block objects, so
it survives the merge.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The merge's block objects at a merge entry (heap `H`). -/
def BlkE (D : BitVec 64 → Prop) (B : Bool) (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64))
    (Ose : BitVec 64 → BitVec 64 → Prop) (Hl H : BitVec 64) (M : Mem) : Prop :=
  (TabRV D B BO lb0 Hl R M ∧ Hl.toNat ≤ H.toNat ∧ lb0.KL = 20#64 ∧ lb0.SD.toNat ≤ 56) ∧ BTF R Ose H M ∧
    ((∀ x, TabPhys BO lb0 x → x.toNat < H.toNat) ∧ (∀ t ∈ R, ∀ x, Ose t x → ¬ TabPhys BO lb0 x))

/-- The regions of the block objects. -/
def BlkRg (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop)
    (x : BitVec 64) : Prop :=
  TabPhys BO lb0 x ∨ ∃ t ∈ R, Ose t x

section bk
variable {D : BitVec 64 → Prop} {B : Bool} {BO : BitVec 64} {lb0 : TLay} {R : Set (BitVec 64)}
  {Ose : BitVec 64 → BitVec 64 → Prop} {Hl H : BitVec 64} {M M' : Mem}

theorem blkE_frame (h : BlkE D B BO lb0 R Ose Hl H M) (keep : ∀ x, BlkRg BO lb0 R Ose x → M' x = M x) :
    BlkE D B BO lb0 R Ose Hl H M' := by
  obtain ⟨⟨rv,a,b,c'⟩,⟨tos,ob,dis⟩,d⟩ := h
  exact ⟨⟨tabRV_frame rv (fun x hx => keep x (Or.inl hx)),a,b,c'⟩,
    ⟨fun t ht => tabO_frame (tos t ht) (fun x hx => keep x (Or.inr ⟨t,ht,hx⟩)),ob,dis⟩,d⟩

theorem blkE_mono {H' : BitVec 64} (h : BlkE D B BO lb0 R Ose Hl H M) (le : H.toNat ≤ H'.toNat) :
    BlkE D B BO lb0 R Ose Hl H' M := by
  obtain ⟨⟨rv,a,b,c'⟩,⟨tos,ob,dis⟩,ph,od⟩ := h
  exact ⟨⟨rv,by omega,b,c'⟩,⟨fun t ht => tabO_mono (tos t ht) le,fun t ht x hx => by have := ob t ht x hx; omega,dis⟩,
    fun x hx => by have := ph x hx; omega,od⟩

theorem mlw_of_blkE {Nj : BitVec 64} {G : GA} (h : BlkE D B BO lb0 R Ose Hl H M) (hH : HeapIs G H)
    (hn : G.lookup (ofString "journal_n") = some (.val (.word Nj))) :
    MLW D B BO lb0 R Ose H Nj M R H Hl lb0 Ose M G := by
  obtain ⟨tr,bt,ph⟩ := h
  exact ⟨⟨hH,le_refl _,hn⟩,tr,bt,ph,⟨fun x hx => Or.inl hx,fun t ht x hx => Or.inl ⟨ht,hx⟩,fun _ h => h⟩,
    fun _ _ _ _ => rfl⟩

#print axioms blkE_frame
#print axioms mlw_of_blkE
end bk

section mw
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H1 : BitVec 64} {Rr Ow : BitVec 64 → Prop}
  {M1 : Mem} {G1 : GA} {BO : BitVec 64} {lb0 : TLay} {R : Set (BitVec 64)} {Ose : BitVec 64 → BitVec 64 → Prop}

/-- The builder world survives the merge: its regions avoid the block objects. -/
theorem uw_of_mlr (wsf : WsIFrame WsI) {R' : Set (BitVec 64)} {M : Mem} {G : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H1 Rr Ow M1 G1)
    (ml : MLR D B BO lb0 R Ose H1 Nj M1 R' M G) (bg : BalG BA IA IS KB Ix G)
    (avoid : ∀ x, ((∃ k, BalK.live ADs k ∧ Rg k x) ∨ Rr x ∨ Ow x) → ¬ BlkRg BO lb0 R Ose x) :
    ∃ H2 : BitVec 64, H1.toNat ≤ H2.toNat ∧ UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H2 Rr Ow M G ∧
      ∀ x, x.toNat < H1.toNat → ¬ BlkRg BO lb0 R Ose x → M x = M1 x := by
  obtain ⟨H2,Hl2,lb2,Os2,⟨hH2,le2,hn2⟩,_,_,_,_,fr⟩ := ml
  obtain ⟨_,_,_,bw,reg,wi,rB,dRO,dis,hsk⟩ := u
  have oB := wsf.2 M1 H1 Ow wi
  have frB : ∀ x, x.toNat < H1.toNat → ¬ BlkRg BO lb0 R Ose x → M x = M1 x := fun x hx hb =>
    fr x (fun h => hb (Or.inl h)) (fun t ht h => hb (Or.inr ⟨t,ht,h⟩)) hx
  refine ⟨H2,le2,⟨hH2,hn2,bg,balW_mono (balW_frame bw (fun k hk x hx =>
      frB x (bw.2.2 k hk x hx) (avoid x (Or.inl ⟨k,hk,hx⟩)))) le2,
    regTR_mono (regTR_frame reg (fun x hx => frB x (rB x hx) (avoid x (Or.inr (Or.inl hx))))) le2,
    wsf.1 M1 H1 Ow M H2 wi (fun x hx => frB x (oB x hx) (avoid x (Or.inr (Or.inr hx)))) le2,
    fun x hx => by have := rB x hx; omega,dRO,dis,hsk⟩,frB⟩

#print axioms uw_of_mlr
end mw
/-- Exit of `incorporate_tx_into_block`: the builder world at the exit (regions grown only by fresh heap), the merge
block objects stepped from the builder exit, and memory below the entry heap outside both region sets unchanged. -/
def IBPost (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB Ix : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop)
    (Sk : BitVec 64 → Prop) (Nj : BitVec 64) (ADs0 : Set (BitVec 64)) (Rg0 : BalK → BitVec 64 → Prop)
    (H0 : BitVec 64) (Rr0 Ow0 : BitVec 64 → Prop) (M0 : Mem) (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64))
    (Ose : BitVec 64 → BitVec 64 → Prop) (M : Mem) (G : GA) : Prop :=
  (∃ (ADs' : Set (BitVec 64)) (Rg' : BalK → BitVec 64 → Prop) (H' : BitVec 64) (Rr' Ow' : BitVec 64 → Prop),
    UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs' Rg' H' Rr' Ow' M G ∧ H0.toNat ≤ H'.toNat ∧ ADs0 ⊆ ADs' ∧
    (∀ k, BalK.live ADs' k → ∀ x, Rg' k x → (BalK.live ADs0 k ∧ Rg0 k x) ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    (∀ x, Rr' x → Rr0 x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    (∀ x, Ow' x → Ow0 x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat))) ∧
  (∃ (M1 : Mem) (H1 : BitVec 64) (R' : Set (BitVec 64)), H0.toNat ≤ H1.toNat ∧
    MLR D B BO lb0 R Ose H1 Nj M1 R' M G) ∧
  ∀ x, x.toNat < H0.toNat → (∀ k, BalK.live ADs0 k → ¬ Rg0 k x) → ¬ Rr0 x → ¬ Ow0 x →
    ¬ BlkRg BO lb0 R Ose x → M x = M0 x

section ic
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}
  {G1 : GA}

theorem incorporateBody_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (u0 : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 G1)
    -- source tables of the builder
    (Taw : BitVec 64) (law : TLay) (cAw : D (Ts + 16#64) ∧ M0 (Ts + 16#64) = .word Taw)
    (tcA : TCont D B M0 Taw law) (klA : 20 ≤ law.KL.toNat) (ncA : law.N.toNat < law.C.toNat)
    (hAwR : ∀ x, InTabF Taw law.KS law.SD law.C law.US law.VS law.OS law.OPS x → UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (Tout : BitVec 64) (lout : TLay) (cOut : D (Ts + 32#64) ∧ M0 (Ts + 32#64) = .word Tout ∧
      UOut ADs0 Rg0 H0 Rr0 Ow0 (Ts + 32#64))
    (tcO : TCont D B M0 Tout lout) (klO : 20 ≤ lout.KL.toNat) (ncO : lout.N.toNat < lout.C.toNat)
    (hOutR : ∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (hIn : ∀ I slot vv : BitVec 64, I.toNat < lout.N.toNat → M0 (lout.OS + I * 8) = .word slot →
      M0 (lout.VS + slot * 8) = .word vv → ∃ li : TLay, (TCont D B M0 vv li ∧ 20 ≤ li.KL.toNat ∧
        li.N.toNat < li.C.toNat) ∧ ∀ x, InTabF vv li.KS li.SD li.C li.US li.VS li.OS li.OPS x →
          UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    -- block objects of the merge
    (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop) (Hl : BitVec 64)
    (blk0 : BlkE D B BO lb0 R Ose Hl H0 M0)
    (hBlk : ∀ x, BlkRg BO lb0 R Ose x → UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (hOutB : ∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → ¬ BlkRg BO lb0 R Ose x)
    (hcell : ∀ k : BitVec 64, k = 8#64 ∨ k = 16#64 ∨ k = 24#64 ∨ k = 32#64 ∨ k = 40#64 ∨ k = 48#64 →
      (D (Bs + k) ∧ (∀ t ∈ R, ¬ Ose t (Bs + k)) ∧ (Bs + k).toNat < H0.toNat) ∧
      (D (Ts + k) ∧ (∀ t ∈ R, ¬ Ose t (Ts + k)) ∧ (Ts + k).toNat < H0.toNat))
    (j24 j8 j40 j16 j48 : BitVec 64) (hj24 : j24 ∈ R) (hj8 : j8 ∈ R) (hj40 : j40 ∈ R) (hj16 : j16 ∈ R)
    (hj48 : j48 ∈ R)
    (cbs : M0 (Bs + 24#64) = .word j24 ∧ M0 (Bs + 8#64) = .word j8 ∧ M0 (Bs + 40#64) = .word j40 ∧
      M0 (Bs + 16#64) = .word j16 ∧ M0 (Bs + 48#64) = .word j48 ∧ M0 (Bs + 32#64) = .word BO)
    (cbsOut : ∀ k : BitVec 64, k = 8#64 ∨ k = 16#64 ∨ k = 24#64 ∨ k = 32#64 ∨ k = 40#64 ∨ k = 48#64 →
      UOut ADs0 Rg0 H0 Rr0 Ow0 (Bs + k))
    (hwB : ¬ BlkRg BO lb0 R Ose w)
    (hwP : w.toNat < P0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun _ M G => M = M0 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧
        IBPost D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 BO lb0 R Ose M G)
      (sourceFunctionBody Guest.guestFn_incorporate_tx_into_block) := by
  have p0 : P0.toNat ≤ H0.toNat ∨ True := Or.inr trivial
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_incorporate_tx_into_block,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_nil,Option.map_none]
  -- update_builder_from_tx()
  refine aqgd_seq (Q := fun L M G => True ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
    (aqgd_conseq (aqgd_call_post (LP := fun _ => True) _ _ _ _ _ originalRuntimeCode_updateBuilderFromTx_lookup
      (fun _ => True) M0 G1 (aqgd_conseq (updateBuilder_aqgd bk wsr ne Bs hBs hcB ne40 Ts hTs hc40 hSkSO hSk u0 Taw law cAw
        tcA klA ncA hAwR Tout lout cOut tcO klO ncO hOutR hIn hwP hwk0 hwR0 hwO0 Dall)
        (fun _ _ _ h => h.2) (fun _ _ _ h => h) (fun _ _ _ h => h.2))
      (fun _ _ _ _ _ _ _ _ _ => trivial))
      (fun _ _ _ h => ⟨trivial,h⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)) ?_
  refine aqgd_ghostR (fun M1 G1' st => ?_)
  obtain ⟨A1,R1,H1,Rr1,Ow1,u1,le1,sub1,gr1,grR1,grO1,fr1⟩ := st
  have keep : ∀ x, UOut ADs0 Rg0 H0 Rr0 Ow0 x → M1 x = M0 x := fun x ⟨a,b,c',d⟩ => fr1 x a b c' d
  have blk1 := blkE_mono (blkE_frame blk0 (fun x hx => keep x (hBlk x hx))) le1
  have u1' := u1
  obtain ⟨hH1,hn1,bg1,_⟩ := u1'
  have tcO1 : TCont D B M1 Tout lout := tcO.frame ncO.le (fun x hx => keep x (hOutR x hx))
  refine uw_heapFact (P := fun _ _ _ => True) u1 (fun ⟨p1,_,_⟩ => ?_)
  obtain ⟨c24,c8,c40,c16,c48,c32⟩ := cbs
  have k1 : ∀ k : BitVec 64, k = 8#64 ∨ k = 16#64 ∨ k = 24#64 ∨ k = 32#64 ∨ k = 40#64 ∨ k = 48#64 →
      M1 (Bs + k) = M0 (Bs + k) := fun k hk => keep _ (cbsOut k hk)
  refine aqgd_seq (Q := fun L M G => (True ∧ ∃ R' : Set (BitVec 64), MLR D B BO lb0 R Ose H1 Nj M1 R' M G) ∧
      BalG BA IA IS KB Ix G)
    (aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_post (LP := fun _ => True) _ _ _ _ _ originalRuntimeCode_mergeTxIntoBlock_lookup (fun _ => True) M1 G1'
        (aqgd_conseq (mergeBody_aqgd BO lb0 R Ose H1 Hl Nj M1 G1' (mlw_of_blkE blk1 hH1 hn1) Tout lout tcO1 klO ncO
          (fun x hx => ⟨fun h => hOutB x hx (Or.inl h),fun t ht h => hOutB x hx (Or.inr ⟨t,ht,h⟩),
            by have := (hOutR x hx).1; omega⟩) Ts Bs hTs hBs
          (fun k hk => let ⟨⟨a1,a2,a3⟩,⟨b1,b2,b3⟩⟩ := hcell k hk; ⟨⟨a1,a2,by omega⟩,⟨b1,b2,by omega⟩⟩)
          j24 j8 j40 j16 j48 hj24 hj8 hj40 hj16 hj48
          (by rw [k1 _ (by simp)]; exact c24) (by rw [k1 _ (by simp)]; exact c8) (by rw [k1 _ (by simp)]; exact c40)
          (by rw [k1 _ (by simp)]; exact c16) (by rw [k1 _ (by simp)]; exact c48)
          (by rw [keep _ cOut.2.2]; exact cOut.2.1) (by rw [k1 _ (by simp)]; exact c32)
          (fun h => hwB (Or.inl h)) (fun t ht h => hwB (Or.inr ⟨t,ht,h⟩)) hwP p1 Dall)
          (fun _ _ _ h => h.2) (fun _ _ _ h => h) (fun _ _ _ h => h.2))
        (fun _ _ _ _ _ _ _ _ _ => trivial)))
      (fun L M G h => ⟨h,by rw [h.2.2]; exact bg1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h.1)) ?_
  refine aqgd_return _ (fun s v H' _ hG ⟨⟨_,R',ml⟩,bg⟩ _ ev => ?_)
  simp [EV,evalHOLExact] at ev
  unfold GIs at hG; subst hG
  have avoid : ∀ x, ((∃ k, BalK.live A1 k ∧ R1 k x) ∨ Rr1 x ∨ Ow1 x) → ¬ BlkRg BO lb0 R Ose x := by
    intro x hx hb
    obtain ⟨xa,xb,xc,xd⟩ := hBlk x hb
    rcases hx with ⟨k,hk,hr⟩ | hr | ho
    · rcases gr1 k hk x hr with ⟨l1,h1⟩ | ⟨a1,_⟩
      · exact xb k l1 h1
      · omega
    · rcases grR1 x hr with h | ⟨a1,_⟩
      · exact xc h
      · omega
    · rcases grO1 x ho with h | ⟨a1,_⟩
      · exact xd h
      · omega
  obtain ⟨H2,le2,u2,frB⟩ := uw_of_mlr wsr.1 u1 ml bg avoid
  refine ⟨ev.symm,⟨A1,R1,H2,Rr1,Ow1,u2,by omega,sub1,fun k hk x hx => ?_,fun x hx => ?_,fun x hx => ?_⟩,
    ⟨M1,H1,R',le1,ml⟩,fun x hx hk hr ho hb => (frB x (by omega) hb).trans (fr1 x hx hk hr ho)⟩
  · rcases gr1 k hk x hx with h | ⟨a1,b1⟩
    · exact Or.inl h
    · exact Or.inr ⟨a1,by omega⟩
  · rcases grR1 x hx with h | ⟨a1,b1⟩
    · exact Or.inl h
    · exact Or.inr ⟨a1,by omega⟩
  · rcases grO1 x hx with h | ⟨a1,b1⟩
    · exact Or.inl h
    · exact Or.inr ⟨a1,by omega⟩

#print axioms incorporateBody_aqgd

end ic
end InitECandidate.Runtime
