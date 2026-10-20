import InitECandidate.Runtime.PtRestOGD
import InitECandidate.Runtime.PtRestAllGD
/-!
`ptRest134` with the interpreter output record threaded: the local `out = Y` (`LPSo`) and the record marks
`out + 80`, `out + 88` (outside words not in `Excl`, kept by the suffix frames from the base memory, where they satisfy
`OutRec`). The frame release needs no further obligation; `incorporate_tx_into_block()` is the named staging contract
`IncorpCO` (keeps `out = Y`, the final suffix state and both block lists).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Named frame contract of `incorporate_tx_into_block()` at the suffix call site (staging): from the final suffix state
with `out = Y`, both block lists and the block-access-list validity `BV` (block objects, writable words in `Excl`), the
same state with the output validity `BVo` (the block objects for the next transaction). -/
def IncorpCO (D : BitVec 64 → Prop) (B : Bool) (w : BitVec 64) (RR : ValueHOL 64 → Mem → GA → Prop)
    (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (Excl W40 W72 : BitVec 64 → Prop) (BV BVo : Mem → Prop) (M0 : Mem)
    (Y Ix Hb L40 L72 : BitVec 64) : Prop :=
  ∀ Hg : BitVec 64, AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
    (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BV M)
    (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BVo M) RR
    (.call (some (none,none)) (ofString "incorporate_tx_into_block") [])

theorem pz_excl {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {D : BitVec 64 → Prop}
    {B : Bool} {Excl Excl' : BitVec 64 → Prop} {Lo Hg : BitVec 64} {M0 M : Mem} {G : GA}
    (h : PZ n c T Out ko D B Excl Lo Hg M0 M G) (sub : ∀ x, Excl x → Excl' x) :
    PZ n c T Out ko D B Excl' Lo Hg M0 M G :=
  let ⟨Hb',Nj,le,hh,reg,hn,fr⟩ := h; ⟨Hb',Nj,le,hh,reg,hn,fun x ho hx => fr x ho (fun e => hx (sub x e))⟩

section ra
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual remainder `ptRest134` of `process_transaction` from the suffix state at `del`. -/
theorem ptRest134O {QM : Mem → GA → Prop} (Y Ix L40 L72 Hb Nj Nl Lp : BitVec 64)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) (hP0Hb : P0.toNat ≤ Hb.toNat)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (hW40 : ∀ x, W40 x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hW72 : ∀ x, W72 x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (Wbal : BitVec 64 → Prop) (BV BVo : Mem → Prop)
    (hWb : ∀ x, Wbal x → Out x ∧ ¬ Excl x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hBVf : ∀ M M', BV M → (∀ x, Wbal x → M' x = M x) → BV M') (hBV0 : BV M0)
    (hinc : IncorpCO D B w RR SP0 P0 FM G0 J C SKB Bo U Sc n c T Out ko (fun x => Excl x ∨ Wbal x) W40 W72 BV BVo M0 Y
      Ix Hb L40 L72)
    (hORm : OutRec SP0 FM Y M0)
    (hYO : (Out (Y + 80#64) ∧ ¬ (Excl (Y + 80#64) ∨ Wbal (Y + 80#64))) ∧
      (Out (Y + 88#64) ∧ ¬ (Excl (Y + 88#64) ∨ Wbal (Y + 88#64))))
    (hRet : ∀ (Hg : BitVec 64) L M G, (LPSo Y Ix L ∧ PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧
      BL2 W40 W72 Hb L40 L72 M G ∧ BVo M → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR ptRest134 := by
  unfold ptRest134
  refine aqgd_conseqA (P' := fun L M G => ∃ Hg : BitVec 64, (LPSo Y Ix L ∧
      PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G ∧ BV M)
    (aqgd_exE (fun Hg => ?_)) ?_
  · refine ptRest_delO (R := fun M G => BL2 W40 W72 Hb L40 L72 M G ∧ BV M) Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco
      hcd hc16 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0
      (fun x hx => Or.inl (hJE x hx)) (fun x hx => Or.inl (hSE x hx)) hP0Hb ECH hECH
      (fun M M' G G' H H' ⟨bls,bv⟩ hH hH' le keep => ⟨⟨bl_frameX bls.1 hW40 hH hH' le keep,
        bl_frameX bls.2 hW72 hH hH' le keep⟩,hBVf M M' bv (fun x hx => let k := hWb x hx;
          keep x (Or.inl k.1) k.2.2.1 k.2.2.2)⟩) ?_
    refine aqgd_seq (hinc Hg) (aqgd_conseq (P := fun L M G =>
        ((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
          PZ n c T Out ko D B (fun x => Excl x ∨ Wbal x) Hb Hg M0 M G) ∧
          (BL2 W40 W72 Hb L40 L72 M G ∧ BVo M) ∧ OutRec SP0 FM Y M)
      (ptRest_tailO Ix Y
        (fun M G gname y hg ⟨bls,bv⟩ => by
          have hn : ofString "heap_ptr" ≠ gname := by rcases hg with rfl | rfl <;> decide
          exact ⟨⟨bl_gupd bls.1 _ _ hn,bl_gupd bls.2 _ _ hn⟩,bv⟩)
        (fun L M G ⟨⟨lp,pz⟩,bls,bv⟩ => hRet Hg L M G ⟨⟨lp,pz⟩,bls,bv⟩)) ?_ (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    intro L M G ⟨⟨lp,pz⟩,bls,bv⟩
    have fr : ∀ x, Out x → ¬ (Excl x ∨ Wbal x) → M x = M0 x := by obtain ⟨_,_,_,_,_,_,fr⟩ := pz; exact fr
    have k80 := fr _ hYO.1.1 hYO.1.2
    have k88 := fr _ hYO.2.1 hYO.2.2
    refine ⟨⟨⟨lp,lp.2⟩,pz⟩,⟨bls,bv⟩,?_⟩
    unfold OutRec at hORm ⊢
    rw [k80,k88]; exact hORm
  · intro L M G _ ⟨⟨ld,pb⟩,b40,b72⟩
    obtain ⟨H,hH,_⟩ := pb.1
    have frB : ∀ x, Wbal x → M x = M0 x := fun x hx => pb.2.2.2 x (hWb x hx).1 (hWb x hx).2.1
    exact ⟨H,⟨ld.1,pz_excl (pz_of_pb hAB pb hH) (fun x h => Or.inl h)⟩,⟨b40,b72⟩,
      hBVf M0 M hBV0 (fun x hx => frB x hx)⟩

#print axioms ptRest134O
end ra
end InitECandidate.Runtime
