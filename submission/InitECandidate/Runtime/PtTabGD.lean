import InitECandidate.Runtime.PtHtabNewGD
/-!
Fresh hash tables of the `process_transaction` segment (`aa`, `ak`): `TabV Tt A P M` is a valid `htab` layout at `Tt`
whose header and arrays lie in `[A, P)` (its canonical footprint at the bound `P`), with the header in memory. It is
monotone in `P`, framed by `[A, P)`, established from `htab_new` (`NewTab`), and kept by the actual `htab_set`
(`set_aqmh`, the arena bound raised to the current heap pointer): a set changes only words at or above `A` and leaves
a valid layout whose arrays are old or fresh, so the segment state `SI` (`A ≥ Lo`) and any memory property framed
below `A` survive.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A valid table at `Tt` with header and arrays in `[A, P)`. -/
def TabV (Tt A P : BitVec 64) (M : Mem) : Prop :=
  ∃ (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat),
    HLay P Tt (Canon Tt C SD KS VS US OS OPS P) KL SD C N KS VS US OS OPS b ∧ Hdr M Tt KL SD C N KS VS US OS OPS ∧
    A.toNat ≤ Tt.toNat ∧ LayIn (fun x => A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) C SD KS VS US OS OPS

theorem tabV_mono {Tt A P P' : BitVec 64} {M : Mem} (h : TabV Tt A P M) (le : P.toNat ≤ P'.toNat) :
    TabV Tt A P' M :=
  let ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩ := h
  ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,hlay_canon lay le,hd,a,fun x hx => let ⟨h1,h2⟩ := li x hx; ⟨h1,by omega⟩⟩

theorem tabV_frame {Tt A P : BitVec 64} {M M' : Mem} (h : TabV Tt A P M)
    (keep : ∀ x : BitVec 64, A.toNat ≤ x.toNat → x.toNat < P.toNat → M' x = M x) : TabV Tt A P M' := by
  obtain ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hd,a,li⟩ := h
  have := lay.hdrP
  refine ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hdr_keep hd (by omega) (fun x lo hi => keep x (by omega) (by omega)),a,li⟩

/-- The canonical footprint at a heap pointer `Hc ≥ A` lies at or above `A`. -/
theorem canon_ge {Tt A C SD KS VS US OS OPS Hc x : BitVec 64}
    (a : A.toNat ≤ Tt.toNat) (li : LayIn (fun x => A.toNat ≤ x.toNat ∧ x.toNat < Hc.toNat) C SD KS VS US OS OPS)
    (hA : A.toNat ≤ Hc.toNat) (hx : Canon Tt C SD KS VS US OS OPS Hc x) : A.toNat ≤ x.toNat := by
  rcases hx with ⟨h,_⟩ | h | h
  · omega
  · exact (li x h).1
  · omega

/-- A fresh `htab_new` table is valid. -/
theorem tabV_ofNew {Tt H' KL Cp A : BitVec 64} {M : Mem} {b : Nat} (h : NewTab Tt H' KL Cp M)
    (hT : Tt.toNat + 72 ≤ H'.toNat) (hE : H'.toNat ≤ 33806089496) (hA : A.toNat ≤ Tt.toNat)
    (pow : Cp.toNat = 2 ^ b) (fits : KL.toNat ≤ ((KL + 7#64) &&& (0#64 - 8#64)).toNat)
    (sdAl : ((KL + 7#64) &&& (0#64 - 8#64)).toNat % 8 = 0)
    (mulK : (Cp * ((KL + 7#64) &&& (0#64 - 8#64))).toNat = Cp.toNat * ((KL + 7#64) &&& (0#64 - 8#64)).toNat)
    (mul8 : (Cp * 8#64).toNat = Cp.toNat * 8) : TabV Tt A H' M := by
  obtain ⟨KS,VS,US,OS,OPS,hd,ksAl,usAl,k1,k2,v1,v2,u1,u2,o1,o2,p1,p2⟩ := h
  have cpos : 0 < Cp.toNat := by rw [pow]; exact Nat.pow_pos (by decide)
  refine ⟨KL,(KL + 7#64) &&& (0#64 - 8#64),Cp,0#64,KS,VS,US,OS,OPS,b,⟨pow,fits,sdAl,ksAl,usAl,by simp; omega,
    fun x lo hi => Or.inl ⟨lo,hi⟩,hT,by omega,fun x hx => Or.inr (Or.inr hx),?_,?_,?_,?_,?_⟩,hd,hA,?_⟩
  · exact ⟨by omega,by rw [← mulK]; omega,fun x lo hi => Or.inr (Or.inl (Or.inl ⟨lo,hi⟩))⟩
  · exact ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inl ⟨lo,by omega⟩)))⟩
  · exact ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))))⟩
  · exact ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,by omega⟩)))))⟩
  · exact ⟨by omega,by omega,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨lo,by omega⟩)))))⟩
  · intro x hx
    rcases hx with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
    · exact ⟨by omega,by rw [← mulK] at hi; omega⟩
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩
    · exact ⟨by omega,by omega⟩

#print axioms tabV_ofNew

/-- A set's post (`SetPost` against the canonical footprint at `Hc`) from a table valid in `[A, P)`, `P ≤ Hc`,
gives a table valid in `[A, H')` and the memory below `A` kept. -/
theorem tabV_set {Tt A P Hc H' SD C KS VS US OS OPS : BitVec 64} {M M' : Mem}
    (a : A.toNat ≤ Tt.toNat) (li : LayIn (fun x => A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) C SD KS VS US OS OPS)
    (hP : P.toNat ≤ Hc.toNat) (hA : A.toNat ≤ P.toNat)
    (post : SetPost Tt (Canon Tt C SD KS VS US OS OPS Hc) M C SD KS VS US OS OPS Hc M' H') :
    TabV Tt A H' M' ∧ Hc.toNat ≤ H'.toNat ∧ ∀ x : BitVec 64, x.toNat < A.toNat → M' x = M x := by
  obtain ⟨le,fr,KL',SD',C',N',KS',VS',US',OS',OPS',b',lay',hd',li'⟩ := post
  refine ⟨⟨KL',SD',C',N',KS',VS',US',OS',OPS',b',lay',hd',a,fun x hx => ?_⟩,le,fun x hx => fr x (fun hc => ?_)⟩
  · rcases li' x hx with h | ⟨h1,h2⟩
    · have := li x h; exact ⟨this.1,by omega⟩
    · exact ⟨by omega,h2⟩
  · have := canon_ge a (fun y hy => let ⟨h1,h2⟩ := li y hy; ⟨h1,by omega⟩) (by omega) hc
    omega

#print axioms tabV_set

/-- The set frame: words outside `[A, P)` below the entry heap pointer `Hc` are kept. -/
theorem set_frame_out {Tt A P Hc H' C SD KS VS US OS OPS : BitVec 64} {M M' : Mem}
    (a : A.toNat ≤ Tt.toNat) (li : LayIn (fun x => A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) C SD KS VS US OS OPS)
    (hdrP : Tt.toNat + 72 ≤ P.toNat)
    (post : SetPost Tt (Canon Tt C SD KS VS US OS OPS Hc) M C SD KS VS US OS OPS Hc M' H') :
    ∀ x : BitVec 64, ¬ (A.toNat ≤ x.toNat ∧ x.toNat < P.toNat) → x.toNat < Hc.toNat → M' x = M x := by
  intro x hx hc
  refine post.2.1 x (fun h => hx ?_)
  rcases h with ⟨h1,h2⟩ | h | h
  · exact ⟨by omega,by omega⟩
  · exact li x h
  · omega

#print axioms set_frame_out
end InitECandidate.Runtime
