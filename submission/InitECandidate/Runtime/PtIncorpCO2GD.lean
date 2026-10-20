import InitECandidate.Runtime.PtRegSubGD
import InitECandidate.Runtime.PtRestAllOGD
/-!
`IncorpCO2`: the staging contract of `incorporate_tx_into_block()` at the reachable state, with block validity over
memory and globals (`BV BVo : Mem → GA → Prop`). Discharged here by the actual installed call: at the call the
builder world runs over the sub-registry `e` of the tables the builder writes (restricted from the suffix registry
`PZ`, region read off memory), so the builder's source tables (registry tables outside the restriction) are outside
objects; the incoming world invariant is `IncW`. The call keeps `PZ` (the whole registry re-extended at the exit heap,
the tables outside the restriction framed; outside words outside `Excl` by the joint frame), both block lists, and
gives the exit world `IncWo`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The staging contract with block validity over memory and globals. -/
def IncorpCO2 (D : BitVec 64 → Prop) (B : Bool) (w : BitVec 64) (RR : ValueHOL 64 → Mem → GA → Prop)
    (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (Excl W40 W72 : BitVec 64 → Prop) (BV BVo : Mem → GA → Prop) (M0 : Mem)
    (Y Ix Hb L40 L72 : BitVec 64) : Prop :=
  ∀ Hg : BitVec 64, AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
    (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BV M G)
    (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BVo M G) RR
    (.call (some (none,none)) (ofString "incorporate_tx_into_block") [])

/-- The registry region read off memory together with an extra owned region. -/
def IRr (n : Nat) (c T : Fin n → BitVec 64) (M : Mem) (Rx : BitVec 64 → Prop) (x : BitVec 64) : Prop :=
  RegRgM n c T M x ∨ Rx x

/-- All regions the incorporation writes. -/
def IWRg (ADs : Set (BitVec 64)) (Rg : BalK → BitVec 64 → Prop) (Rr Ow : BitVec 64 → Prop) (BO : BitVec 64)
    (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop) (x : BitVec 64) : Prop :=
  (∃ k, BalK.live ADs k ∧ Rg k x) ∨ Rr x ∨ Ow x ∨ BlkRg BO lb0 R Ose x

/-- The incoming world of the incorporation at the call, over the sub-registry `e` (content table `e ko'`): the
block-access-list objects, the witness invariant and scratch region, the builder source tables and the merge block
objects, all separated from each other and from the sub-registry region; the regions below the watch bound `Pw`
inside `Z`; the outside words outside `Excl`, the block-list words and the footprints of the registry tables outside
the sub-registry off every region and below the heap. -/
def IncW (D : BitVec 64 → Prop) (B : Bool) (n m : Nat) (c T : Fin n → BitVec 64) (e : Fin m → Fin n) (ko' : Fin m)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (Sk : BitVec 64 → Prop) (Ts Bs Pw : BitVec 64)
    (Z Out Excl W40 W72 : BitVec 64 → Prop) (M : Mem) (G : GA) : Prop :=
  ∃ (BA IA IS KB Ix : BitVec 64) (ADs : Set (BitVec 64)) (Rg : BalK → BitVec 64 → Prop) (H : BitVec 64)
    (Ow Rx : BitVec 64 → Prop) (Taw : BitVec 64) (law : TLay) (Tout : BitVec 64) (lout : TLay) (BO : BitVec 64)
    (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop) (Hl j24 j8 j40 j16 j48 : BitVec 64),
    -- the world without the registry
    (HeapIs G H ∧ BalG BA IA IS KB Ix G ∧ BalW D B BA IA IS KB ADs Rg H M ∧ WsI M H Ow ∧
      (∀ x, Rx x → x.toNat < H.toNat) ∧ (∀ x, Ow x → ¬ (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) x) ∧
      (∀ k, BalK.live ADs k → ∀ x, Rg k x → ¬ (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) x ∧ ¬ Ow x) ∧ ∀ x, Sk x → (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) x) ∧
    -- the builder source tables
    ((D (Ts + 16#64) ∧ M (Ts + 16#64) = .word Taw) ∧ TCont D B M Taw law ∧ 20 ≤ law.KL.toNat ∧
      law.N.toNat < law.C.toNat ∧
      (∀ x, InTabF Taw law.KS law.SD law.C law.US law.VS law.OS law.OPS x → UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow x) ∧
      (D (Ts + 32#64) ∧ M (Ts + 32#64) = .word Tout ∧ UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow (Ts + 32#64)) ∧
      TCont D B M Tout lout ∧ 20 ≤ lout.KL.toNat ∧ lout.N.toNat < lout.C.toNat ∧
      (∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow x) ∧
      ∀ I slot vv : BitVec 64, I.toNat < lout.N.toNat → M (lout.OS + I * 8) = .word slot →
        M (lout.VS + slot * 8) = .word vv → ∃ li : TLay, (TCont D B M vv li ∧ 20 ≤ li.KL.toNat ∧
          li.N.toNat < li.C.toNat) ∧ ∀ x, InTabF vv li.KS li.SD li.C li.US li.VS li.OS li.OPS x →
            UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow x) ∧
    -- the merge block objects
    (BlkE D B BO lb0 R Ose Hl H M ∧ (∀ x, BlkRg BO lb0 R Ose x → UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow x) ∧
      (∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → ¬ BlkRg BO lb0 R Ose x) ∧
      (∀ k : BitVec 64, k = 8#64 ∨ k = 16#64 ∨ k = 24#64 ∨ k = 32#64 ∨ k = 40#64 ∨ k = 48#64 →
        ((D (Bs + k) ∧ (∀ t ∈ R, ¬ Ose t (Bs + k)) ∧ (Bs + k).toNat < H.toNat) ∧
        (D (Ts + k) ∧ (∀ t ∈ R, ¬ Ose t (Ts + k)) ∧ (Ts + k).toNat < H.toNat)) ∧ UOut ADs Rg H (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow (Bs + k)) ∧
      (j24 ∈ R ∧ j8 ∈ R ∧ j40 ∈ R ∧ j16 ∈ R ∧ j48 ∈ R) ∧
      (M (Bs + 24#64) = .word j24 ∧ M (Bs + 8#64) = .word j8 ∧ M (Bs + 40#64) = .word j40 ∧
        M (Bs + 16#64) = .word j16 ∧ M (Bs + 48#64) = .word j48 ∧ M (Bs + 32#64) = .word BO)) ∧
    -- watchability (below `Pw`) and the outside / block-list words
    (∀ x, IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow BO lb0 R Ose x → x.toNat < Pw.toNat → Z x) ∧
    (∀ x, Out x → ¬ Excl x → x.toNat < H.toNat ∧ ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow BO lb0 R Ose x) ∧
    (∀ x, (W40 x ∨ W72 x) → x.toNat < H.toNat ∧ ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow BO lb0 R Ose x) ∧
    -- the sub-registry's content table, the extra region, the registry tables outside the sub-registry
    (∃ lz : TLay, lz.hdr M (T (e ko')) ∧ lz.C.toNat = 2 ^ lz.b ∧ TCont D B M (T (e ko')) lz) ∧
    (∀ x, Rx x → Out x ∧ ∀ i, x ≠ c i) ∧
    (∀ j, (∀ i, e i ≠ j) → ∀ x, OthFp c T M j x →
      x.toNat < H.toNat ∧ ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow BO lb0 R Ose x)

/-- The exit world of the incorporation: a builder world (some registry outside set) and the merge block objects. -/
def IncWo (D : BitVec 64 → Prop) (B : Bool) (n : Nat) (c T : Fin n → BitVec 64) (ko : Fin n)
    (WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop) (Sk : BitVec 64 → Prop) (M : Mem) (G : GA) : Prop :=
  ∃ (BA IA IS KB Ix Nj : BitVec 64) (Out' : BitVec 64 → Prop) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H : BitVec 64) (Rr Ow : BitVec 64 → Prop),
    UW D B BA IA IS KB Ix n c T Out' ko WsI Sk Nj ADs Rg H Rr Ow M G ∧
    ∃ (BO : BitVec 64) (lb0 : TLay) (R : Set (BitVec 64)) (Ose : BitVec 64 → BitVec 64 → Prop) (M1 : Mem)
      (H1 : BitVec 64) (R' : Set (BitVec 64)), MLR D B BO lb0 R Ose H1 Nj M1 R' M G

section ic2
variable {D : BitVec 64 → Prop} {B : Bool} {n m : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop}
  {ko : Fin n} {e : Fin m → Fin n} {ko' : Fin m} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {BA IA IS KB Ixb : BitVec 64} {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop}
  {H : BitVec 64} {Ow Rx : BitVec 64 → Prop} {Excl : BitVec 64 → Prop} {Hb Hg Hb' Nj : BitVec 64} {Mz : Mem}

/-- The builder world over the sub-registry at the call, restricted from the suffix registry, and the whole registry
at the call heap. -/
theorem uw_of_pzIncW (inj : ∀ i j, e i = e j → i = j) {kA' kB' : Fin m} (hAB' : kA' ≠ kB') {kA kB : Fin n}
    (hAB : kA ≠ kB) {M : Mem} {G : GA} (pg : PG n c T Out ko D B Excl Hb Hg Hb' Nj Mz M G)
    (hH : HeapIs G H) (bg : BalG BA IA IS KB Ixb G) (bw : BalW D B BA IA IS KB ADs Rg H M) (wi : WsI M H Ow)
    (rxB : ∀ x, Rx x → x.toNat < H.toNat)
    (dRO : ∀ x, Ow x → ¬ IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx x)
    (dis : ∀ k, BalK.live ADs k → ∀ x, Rg k x → ¬ IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx x ∧ ¬ Ow x)
    (hsk : ∀ x, Sk x → IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx x)
    (cz : ∃ lz : TLay, lz.hdr M (T (e ko')) ∧ lz.C.toNat = 2 ^ lz.b ∧ TCont D B M (T (e ko')) lz) :
    UW D B BA IA IS KB Ixb m (fun i => c (e i)) (fun i => T (e i)) (OutX Out Hb Hg) ko' WsI Sk Nj ADs Rg H
      (IRr m (fun i => c (e i)) (fun i => T (e i)) M Rx) Ow M G ∧ RegT n c T (OutX Out Hb Hg) H M D B ko := by
  obtain ⟨⟨H2,hH2,le2⟩,reg,hn,_⟩ := pg
  have e := heapIs_unique hH2 hH
  subst e
  have reg' := regT_mono reg le2
  obtain ⟨lz,hz,pz,tz⟩ := cz
  have rs := regT_restrict inj hAB reg' lz hz pz tz
  exact ⟨⟨hH,hn,bg,bw,regTR_sub (regTR_of_regT rs) (fun x h => Or.inl h),wi,
    fun x hx => hx.elim (regRgM_below rs hAB' x) (rxB x),dRO,dis,hsk⟩,reg'⟩

#print axioms uw_of_pzIncW

/-- From the exit of the actual call: the suffix state (whole registry re-extended), both block lists and the exit
world. -/
theorem incorp2_post (inj : ∀ i j, e i = e j → i = j) {kA kB : Fin n} (hAB : kA ≠ kB) (hko : ∀ i, e i ≠ ko)
    {W40 W72 : BitVec 64 → Prop} {L40 L72 : BitVec 64} {BO : BitVec 64}
    {lb0 : TLay} {R : Set (BitVec 64)} {Ose : BitVec 64 → BitVec 64 → Prop} {M1 M : Mem} {G1 G : GA}
    (pg : PG n c T Out ko D B Excl Hb Hg Hb' Nj Mz M1 G1) (hle : Hg.toNat ≤ Hb'.toNat) (hH : HeapIs G1 H)
    (reg0 : RegT n c T (OutX Out Hb Hg) H M1 D B ko) (bl : BL2 W40 W72 Hb L40 L72 M1 G1)
    (hRx : ∀ x, Rx x → Out x ∧ ∀ i, x ≠ c i)
    (hOX : ∀ x, Out x → ¬ Excl x → x.toNat < H.toNat ∧
      ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow BO lb0 R Ose x)
    (hWX : ∀ x, (W40 x ∨ W72 x) → x.toNat < H.toNat ∧
      ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow BO lb0 R Ose x)
    (hOth : ∀ j, (∀ i, e i ≠ j) → ∀ x, OthFp c T M1 j x →
      x.toNat < H.toNat ∧ ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow BO lb0 R Ose x)
    (ib : IBPost D B BA IA IS KB Ixb m (fun i => c (e i)) (fun i => T (e i)) (OutX Out Hb Hg) ko' WsI Sk Nj ADs Rg H
      (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow M1 BO lb0 R Ose M G) :
    PZ n c T Out ko D B Excl Hb Hg Mz M G ∧ BL2 W40 W72 Hb L40 L72 M G ∧
      IncWo D B m (fun i => c (e i)) (fun i => T (e i)) ko' WsI Sk M G := by
  obtain ⟨⟨ADs',Rg',H',Rr',Ow',uw,le,_,_,hRr',_⟩,⟨M1',H1,R',_,mlr⟩,fr⟩ := ib
  obtain ⟨⟨H2,hH2,le2⟩,_,_,frz⟩ := pg
  have e := heapIs_unique hH2 hH
  subst e
  have keep : ∀ x, x.toNat < H2.toNat →
      ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow BO lb0 R Ose x → M x = M1 x :=
    fun x hx hn => fr x hx (fun k hk h => hn (Or.inl ⟨k,hk,h⟩)) (fun h => hn (Or.inr (Or.inl h)))
      (fun h => hn (Or.inr (Or.inr (Or.inl h)))) (fun h => hn (Or.inr (Or.inr (Or.inr h))))
  have hHG : ∀ H, HeapIs G1 H → ∃ H', HeapIs G H' ∧ H.toNat ≤ H'.toNat := fun H h =>
    ⟨H',uw.1,by have := heapIs_unique h hH2; subst this; exact le⟩
  have regX : RegT n c T (OutX Out Hb Hg) H' M D B ko := regT_extend inj hAB reg0 hko uw.2.2.2.2.1 le
    (fun x hx => by
      rcases hRr' x hx with h | h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun x h => ⟨Or.inl (hRx x h).1,(hRx x h).2⟩)
    (fun j hj x hx => keep x (hOth j hj x hx).1 (hOth j hj x hx).2)
  refine ⟨⟨H',Nj,by omega,⟨H',uw.1,le_refl _⟩,regX,uw.2.1,fun x ho he => ?_⟩,
    ⟨bl_frame bl.1 (fun x hx => ?_) hHG,bl_frame bl.2 (fun x hx => ?_) hHG⟩,
    ⟨BA,IA,IS,KB,Ixb,Nj,OutX Out Hb Hg,ADs',Rg',H',Rr',Ow',uw,BO,lb0,R,Ose,M1',H1,R',mlr⟩⟩
  · exact (keep x (hOX x ho he).1 (hOX x ho he).2).trans (frz x ho he)
  · exact keep x (hWX x (Or.inl (bl.1.1 x hx))).1 (hWX x (Or.inl (bl.1.1 x hx))).2
  · exact keep x (hWX x (Or.inr (bl.2.1 x hx))).1 (hWX x (Or.inr (bl.2.1 x hx))).2

#print axioms incorp2_post
end ic2

section ic3
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {n m : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Sk : BitVec 64 → Prop}
  {Excl W40 W72 Z : BitVec 64 → Prop} {Mz : Mem} {Y Ix Hb L40 L72 : BitVec 64}

/-- `IncorpCO2` with incoming world `IncW` over the sub-registry `e` (written tables `e kB'` at `bs + 72` and `e k40'`
at `ts + 40`, content table `e ko'`, the suffix content table `ko` outside) and exit world `IncWo`, discharged by the
actual installed `incorporate_tx_into_block()` call. `BalKeep` and the OPEN witness obligation `WsReadObl` stay
explicit. -/
theorem incorpCO2_call (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (e : Fin m → Fin n) (inj : ∀ i j, e i = e j → i = j) (ko' kB' k40' : Fin m) (hko : ∀ i, e i ≠ ko)
    (hAB : kA ≠ kB) (ne : kB' ≠ ko') (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c (e kB') = Bs + 72#64) (ne40 : k40' ≠ ko') (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c (e k40') = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (Pw : BitVec 64) (hwZ : ¬ Z w) (hwPw : w.toNat < Pw.toNat) (hwP : w.toNat < P0.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    IncorpCO2 D B w RR SP0 P0 FM G0 J C SKB Bo U Sc n c T Out ko Excl W40 W72
      (fun M G => IncW D B n m c T e ko' WsI Sk Ts Bs Pw Z Out Excl W40 W72 M G)
      (fun M G => IncWo D B m (fun i => c (e i)) (fun i => T (e i)) ko' WsI Sk M G) Mz Y Ix Hb L40 L72 := by
  intro Hg
  refine aqgd_conseq (P := fun L M G => LPSo Y Ix L ∧ (PZ n c T Out ko D B Excl Hb Hg Mz M G ∧
      BL2 W40 W72 Hb L40 L72 M G ∧ IncW D B n m c T e ko' WsI Sk Ts Bs Pw Z Out Excl W40 W72 M G))
    (Q := fun L M G => LPSo Y Ix L ∧ (PZ n c T Out ko D B Excl Hb Hg Mz M G ∧
      BL2 W40 W72 Hb L40 L72 M G ∧ IncWo D B m (fun i => c (e i)) (fun i => T (e i)) ko' WsI Sk M G))
    (aqgd_ghostR fun M1 G1 pre => ?_) (fun _ _ _ ⟨⟨lp,pz⟩,bl,iw⟩ => ⟨lp,pz,bl,iw⟩)
    (fun _ _ _ ⟨lp,h⟩ => ⟨⟨lp,h.1⟩,h.2⟩) (fun _ _ _ h => h)
  obtain ⟨⟨Hb',Nj,hle,pg⟩,bl,iw⟩ := pre
  obtain ⟨BA,IA,IS,KB,Ixb,ADs,Rg,H,Ow,Rx,Taw,law,Tout,lout,BO,lb0,R,Ose,Hl,j24,j8,j40,j16,j48,
    ⟨hH,bg,bw,wi,rxB,dRO,dis,hsk⟩,⟨cAw,tcA,klA,ncA,hAwR,cOut,tcO,klO,ncO,hOutR,hIn⟩,
    ⟨blk0,hBlk,hOutB,hcell,⟨hj24,hj8,hj40,hj16,hj48⟩,cbs⟩,hZ,hOX,hWX,cz,hRx,hOth⟩ := iw
  obtain ⟨u0,reg0⟩ := uw_of_pzIncW (Sk := Sk) inj ne hAB pg hH bg bw wi rxB dRO dis hsk cz
  have hwI : ¬ IWRg ADs Rg (IRr m (fun i => c (e i)) (fun i => T (e i)) M1 Rx) Ow BO lb0 R Ose w :=
    fun h => hwZ (hZ w h hwPw)
  exact aqgd_conseq (aqgd_call_incorporate (LP := LPSo Y Ix) (RR := RR) bk wsr ne Bs hBs hcB ne40 Ts hTs hc40
      (fun x h => ⟨Or.inl (hSkSO x h).1,fun i => (hSkSO x h).2 (e i)⟩) hSk u0 Taw law cAw tcA klA ncA hAwR Tout lout
      cOut tcO klO ncO hOutR hIn BO lb0 R Ose Hl blk0 hBlk hOutB (fun k hk => (hcell k hk).1) j24 j8 j40 j16 j48
      hj24 hj8 hj40 hj16 hj48 cbs (fun k hk => (hcell k hk).2) (fun h => hwI (Or.inr (Or.inr (Or.inr h)))) hwP
      (fun k hk h => hwI (Or.inl ⟨k,hk,h⟩)) (fun h => hwI (Or.inr (Or.inl h)))
      (fun h => hwI (Or.inr (Or.inr (Or.inl h)))) Dall)
    (fun _ _ _ h => h)
    (fun _ _ _ ⟨lp,ib⟩ => ⟨lp,incorp2_post inj hAB hko pg hle hH reg0 bl hRx hOX hWX hOth ib⟩) (fun _ _ _ h => h)

#print axioms incorpCO2_call
end ic3
end InitECandidate.Runtime
