import InitECandidate.Runtime.RecSenderGD
import InitECandidate.Runtime.ProcessTxUGD
/-!
`RecC` in frame form (`recoverSender_frame`: the actual `recover_sender_with_chain_id` keeps every word below its entry
heap pointer outside `RWin` = sender, Keccak state/pad, accelerator scratch), the scratch-pinned process arena
`JWSBUS` and its converter, and registry/window helpers for the call-site composition.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The words `recover_sender_with_chain_id` may write below its entry heap pointer: the sender `[S, S + 20)`, the
Keccak state and pad, and the accelerator scratch. -/
def RWin (S K Pd Sc : BitVec 64) (x : BitVec 64) : Prop :=
  MWin S 20 x ∨ MWin K 200 x ∨ MWin Pd 136 x ∨ MWin Sc 448 x

section rf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}

/-- `RecC` (frame form): from heap pointer at or above `Lo` and `secp_accel_scratch = Sc`, every return keeps `RG`
and every word below `Lo` outside `RWin` unchanged. -/
theorem recoverSender_frame (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (Lo Sc K Pd S : BitVec 64) (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd))) (hSc0 : Sc ≠ 0)
    (hw : w.toNat < Lo.toNat) (hwW : ¬ RWin S K Pd Sc w) (M0 : Mem) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L M G => (RSL S L ∧ RG Lo Sc G) ∧ M = M0) (fun _ _ _ => False)
      (fun _ M' G' => RG Lo Sc G' ∧ ∀ x, x.toNat < Lo.toNat → ¬ RWin S K Pd Sc x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id) := by
  intro F s code dom aw sl H hH ⟨pre,hM⟩
  subst hM
  have win := fun (x : BitVec 64) (hx : x.toNat < Lo.toNat) (hnx : ¬ RWin S K Pd Sc x) =>
    recoverSender_wn (w := x) (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
      (SKB := SKB) (Nj := Nj) (Q := fun _ _ _ => False) hF hDF hcap Lo Sc K Pd S hK0 hPd0 hx
      (fun h => hnx (Or.inr (Or.inl h))) (fun h => hnx (Or.inr (Or.inr (Or.inl h))))
      (fun h => hnx (Or.inr (Or.inr (Or.inr h)))) hSc0 (fun h => hnx (Or.inl h)) F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := win w hw hwW
  refine ⟨m,a,fun e => ⟨(n e).1,let ⟨_,_,h⟩ := (n e).2; h.elim⟩,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',rg⟩ := r v e
  exact ⟨H',hH',rg,fun x hx hnx => (win x hx hnx).1⟩

#print axioms recoverSender_frame
end rf

/-- The process arena with the accelerator scratch pinned. -/
def JWSBUS (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (g : GA) : Prop :=
  JWSBU SP0 P0 FM G0 J C SKB Bo U g ∧ ScrIs Sc g

section cv
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {SP0 P0 FM J C SKB Bo U Sc Nj : BitVec 64}
  {G0 : GA}

/-- A body that always returns (normal completion impossible), keeps `bo` and `u256_ws`, and returns with
`secp_accel_scratch = Sc`, moves from the pinned-journal arena to the scratch-pinned process arena. -/
theorem aqgd_jwsbus_of_jwsn {P : GA → Mem → GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop} {body : ProgHOL 64}
    (hk : keepsG (ofString "bo") goodBo body = true) (hkw : keepsG (ofString "u256_ws") goodWs body = true)
    (h : AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w Vn P (fun _ _ _ => False) (fun r M G => RR r M G ∧ ScrIs Sc G) body) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn
      (fun L M G => P L M G ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) (fun _ _ _ => False)
      (fun r M G => (RR r M G ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) body := by
  intro F s code dom ⟨⟨⟨jws,hbo⟩,ws⟩,_⟩ sl H hH ⟨pre,hn⟩
  have hn' : s.globals.lookup (ofString "journal_n") = some (.val (.word Nj)) := by
    unfold GIs at hH; rw [hH]; exact hn
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom ⟨jws,hn'⟩ sl H hH pre
  have gbo := evaluate_keepsG _ goodBo goodBo_bodies body hk s code
  have gws := evaluate_keeps_ws body hkw s code
  refine ⟨m,fun cont => ?_,n,fun v e => ?_,c,b⟩
  rotate_left
  · obtain ⟨H',hH',rr⟩ := r v e
    refine ⟨H',hH',rr,?_⟩
    have := (a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))).2
    unfold GIs at hH'; rw [← hH']; exact this
  rcases cont with e | e | e | ⟨v,e⟩
  · obtain ⟨_,_,_,f⟩ := n e; exact f.elim
  · exact absurd e c
  · exact absurd e b
  · obtain ⟨H',hH',_,sc⟩ := r v e
    unfold GIs at hH'
    refine ⟨⟨⟨(a (Or.inr (Or.inr (Or.inr ⟨v,e⟩)))).1,by rw [gbo]; exact hbo⟩,?_⟩,by rw [← hH'] at sc; exact sc⟩
    unfold WsG; rw [gws]; exact ws

#print axioms aqgd_jwsbus_of_jwsn
end cv

section rk
variable {D : BitVec 64 → Prop} {B : Bool}

/-- The registry with content at heap pointer `H` survives memory changes confined to words at or above `H` and to a
set `W` avoiding its pointer cells, headers and the `ko` arrays. -/
theorem regT_keep_except {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (W : BitVec 64 → Prop)
    (keep : ∀ x, x.toNat < H.toNat → ¬ W x → M' x = M x)
    (hcell : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → ¬ W x)
    (hko : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → ¬ W x) :
    RegT n c T Out H M' D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x ?_ (hcell x ⟨i,hx⟩)),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x ?_ (hko M (l ko) (mem ko).2 x hx)),ab⟩
  · rcases hx with rfl | ⟨_,hi⟩
    · by_contra hc
      exact (pure.1 i).2 (Or.inr (Or.inr (by omega)))
    · have := (pure.1 i).1.hdrP; omega
  · rcases hx with ⟨_,hi⟩ | h | h | h | h | h
    · have := (pure.1 ko).1.hdrP; omega
    · exact ab x (Or.inl h)
    · exact ab x (Or.inr (Or.inl h))
    · exact ab x (Or.inr (Or.inr (Or.inl h)))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inr h))))

#print axioms regT_keep_except
end rk

/-- Words below an aligned `S` are outside the byte window `[S, S + n)`. -/
theorem mwin_belowS {S x : BitVec 64} {n : Nat} (hal : S.toNat % 8 = 0) (hfit : S.toNat + n < 2 ^ 64)
    (hx : x.toNat < S.toNat) : ¬ MWin S n x := by
  rintro ⟨j,hj,e | e⟩
  · have : (S + BitVec.ofNat 64 j).toNat = S.toNat + j := by simp [BitVec.toNat_add]; omega
    rw [← e] at this; omega
  · have h1 := align_toNat (S + BitVec.ofNat 64 j)
    have : (S + BitVec.ofNat 64 j).toNat = S.toNat + j := by simp [BitVec.toNat_add]; omega
    rw [this,← e] at h1; omega

end InitECandidate.Runtime
