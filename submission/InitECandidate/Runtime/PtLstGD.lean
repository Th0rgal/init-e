import InitECandidate.Runtime.PtRcptGD
/-!
The actual `lst_new(esz, cap)` (whole-memory form over the pinned-journal arena): returns a fresh 24-byte list
header at or above the entry heap pointer `H`; every word below `H` kept, only `heap_ptr` changes.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ln
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

theorem hn_storeStepN (tn : MlS) (Sz : Nat) {H Tt : BitVec 64} {M0 : Mem} {Gk : GA} {ps : List (MlS × BitVec 64)}
    {cells : List (BitVec 64 × BitVec 64)} {lo : Nat} {RR : ValueHOL 64 → Mem → GA → Prop} (k y : BitVec 64)
    (v : ExpHOL 64) (hk : k.toNat < Sz) (hT : Tt.toNat + Sz ≤ 33806089496) (hHT : H.toNat ≤ Tt.toNat)
    (hw : w.toNat < H.toNat) (ht : ∀ L, LK ps L → L.lookup tn = some (.val (.word Tt)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LK ps s.locals → EV s v = some (.val (.word y)))
    (hnew : ∀ p ∈ cells, p.1 ≠ k) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (HNS H Tt M0 Gk ps cells lo)
      (HNS H Tt M0 Gk ps ((k,y) :: cells) lo) RR (.store (.op .add [.var .local tn,.const k]) v) := by
  have e : (Tt + k).toNat = Tt.toNat + k.toNat := by simp [BitVec.toNat_add]; omega
  refine aqgd_storeD _ _ (fun s G _ _ hG ⟨lk,fr,ce,hh,oh⟩ _ => ?_)
    (fun s x _ _ _ _ pre _ ev => ⟨y,by rw [hv s pre.1] at ev; exact (Option.some.inj ev).symm⟩)
  unfold GIs at hG; subst hG
  refine ⟨Tt + k,ev_addc s _ Tt k (ht _ lk),fun h => by rw [← h] at e; omega,fun y' ev' => ?_⟩
  rw [hv s lk] at ev'
  have hy := (Option.some.inj ev').symm
  simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at hy
  subst hy
  refine ⟨lk,fun x hx => ?_,cellsAt_cons ce hnew,hh,oh⟩
  have : x ≠ Tt + k := fun h => by rw [← h] at e; omega
  simp only [this,if_false]; exact fr x hx

#print axioms hn_storeStepN

theorem lstNew_spec (E Cp H : BitVec 64) (hw : w.toNat < H.toNat) (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (LK [(ofString "cap",Cp),(ofString "esz",E)] L ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk)
      (fun _ _ _ => False)
      (fun v M' G' => (∃ y : BitVec 64, v = .val (.word y)) ∧ (∀ x, x.toNat < H.toNat → M' x = M0 x) ∧
        OnlyHeap Gk G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat ≤ H'.toNat)
      (sourceFunctionBody Guest.guestFn_lst_new) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_lst_new,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  refine aqgd_conseq (P := HNS H H M0 Gk [(ofString "cap",Cp),(ofString "esz",E)] [] H.toNat) ?_
    (fun L M G ⟨⟨lk,hM,hH⟩,hG⟩ => by subst hM hG; exact ⟨lk,fun _ _ => rfl,fun p hp => by simp at hp,⟨H,hH,le_refl _⟩,
      fun _ _ => rfl⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine hn_allocStep (ofString "l") (.const 24) 24#64 (fun s _ => by simp [EV,evalHOLExact])
    (by simp (config := {decide := true})) (fun X alX loX fitX => ?_)
  refine aqgd_conseq (P := HNS H X M0 Gk [(ofString "l",X),(ofString "cap",Cp),(ofString "esz",E)] []
    (X.toNat + (24#64).toNat)) ?_ (fun L M G h => ⟨h.1,h.2.1,fun p hp => by simp at hp,h.2.2.2⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  have h24 : (24#64).toNat = 24 := rfl
  refine hn_allocStep (ofString "p") _ (E * Cp) (fun s lk => by
      simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "esz",E) (by simp),lk (ofString "cap",Cp) (by simp),
        panOpHOL,valueIsWord,valueWord]) (by simp (config := {decide := true})) (fun Pp _ _ _ => ?_)
  have hT : X.toNat + 24 ≤ 33806089496 := by rw [h24] at fitX; exact fitX
  have hHX : H.toNat ≤ X.toNat := loX
  have st := fun (k y : BitVec 64) (v : ExpHOL 64) (hk : k.toNat < 24) (cells : List (BitVec 64 × BitVec 64)) (lo : Nat)
      (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        LK [(ofString "p",Pp),(ofString "l",X),(ofString "cap",Cp),(ofString "esz",E)] s.locals →
        EV s v = some (.val (.word y))) (hnew : ∀ p ∈ cells, p.1 ≠ k) =>
    hn_storeStepN (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (w := w) (H := H) (Tt := X) (M0 := M0) (Gk := Gk) (lo := lo) (RR := fun v M' G' =>
        (∃ y : BitVec 64, v = .val (.word y)) ∧ (∀ x, x.toNat < H.toNat → M' x = M0 x) ∧ OnlyHeap Gk G' ∧
        ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat ≤ H'.toNat) (ofString "l") 24 k y v hk hT hHX hw
      (fun L lk => lk (ofString "l",X) (by simp)) hv hnew
  refine aqgd_seq (st 0#64 Pp _ (by decide) [] _ (fun s lk => by simp [EV,evalHOLExact,lk (ofString "p",Pp) (by simp)])
    (by simp)) ?_
  refine aqgd_seq (st 8#64 0#64 _ (by decide) _ _ (fun s lk => by simp [EV,evalHOLExact]) (by simp)) ?_
  refine aqgd_seq (st 16#64 Cp _ (by decide) _ _ (fun s lk => by simp [EV,evalHOLExact,lk (ofString "cap",Cp) (by simp)])
    (by simp)) ?_
  exact aqgd_return _ (fun s v G' _ hG ⟨lk,fr,_,⟨Hc,hHc,le⟩,oh⟩ _ ev => by
    unfold GIs at hG; subst hG
    simp [EV,evalHOLExact,lk (ofString "l",X) (by simp)] at ev
    subst ev
    exact ⟨⟨X,rfl⟩,fr,oh,Hc,hHc,by omega⟩)

#print axioms lstNew_spec
end ln
end InitECandidate.Runtime
