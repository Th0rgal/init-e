import InitECandidate.Runtime.PtRestGD
/-!
The actual `process_transaction` remainder `ptRest134` from the suffix state at `del` (spine drop 126 heap pointer
`Hb`, both block lists valid): the final suffix state `PZ` over the fresh words `[Hb, Hg)` (`Hg` the heap pointer at
`del`), the deletion loop, `incorporate_tx_into_block()` (named frame contract `IncorpC`, staging), and the frame
release under the named interpreter-output obligation `OutRecObl`, then `return 0`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ra
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- Both block lists over the fresh words `[Hb, Hg)`. -/
def BL2 (W40 W72 : BitVec 64 → Prop) (Hb L40 L72 : BitVec 64) (M : Mem) (G : GA) : Prop :=
  BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G

/-- Named frame contract of `incorporate_tx_into_block()` at the suffix call site (staging): the final suffix state
and both block lists are kept. -/
def IncorpC (D : BitVec 64 → Prop) (B : Bool) (w : BitVec 64) (RR : ValueHOL 64 → Mem → GA → Prop)
    (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (Excl W40 W72 : BitVec 64 → Prop) (M0 : Mem) (Ix Hb L40 L72 : BitVec 64) :
    Prop :=
  ∀ Hg : BitVec 64, AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
    (fun L M G => (LPS Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G)
    (fun L M G => (LPS Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G) RR
    (.call (some (none,none)) (ofString "incorporate_tx_into_block") [])

/-- Named interpreter-output obligation (staging): at the frame release the local `out` is the word `Y` of the
interpreter's output record, which satisfies `OutRec`. -/
def OutRecObl (D : BitVec 64 → Prop) (B : Bool) (SP0 FM : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (Excl W40 W72 : BitVec 64 → Prop) (M0 : Mem) (Ix Hb L40 L72 : BitVec 64) :
    Prop :=
  ∀ (Hg : BitVec 64) (L : GA) (M : Mem) (G : GA),
    (LPS Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧ BL2 W40 W72 Hb L40 L72 M G →
      ∃ Y : BitVec 64, L.lookup (ofString "out") = some (.val (.word Y)) ∧ OutRec SP0 FM Y M

theorem bl_frameX {Wb : BitVec 64 → Prop} {Hb Lh Lo Hg H H' : BitVec 64} {M M' : Mem} {G G' : GA}
    (h : BL Wb Hb Lh 8#64 M G) (hW : ∀ x, Wb x → Out x ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x)
    (hH : HeapIs G H) (hH' : HeapIs G' H') (le : H.toNat ≤ H'.toNat)
    (keep : ∀ x, OutX Out Lo Hg x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M x) : BL Wb Hb Lh 8#64 M' G' :=
  bl_frame h (fun x hx => let k := hW x (h.1 x hx); keep x (Or.inl k.1) k.2.1 k.2.2)
    (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩)

theorem bl_gupd {Wb : BitVec 64 → Prop} {Hb Lh : BitVec 64} {M : Mem} {G : GA} (h : BL Wb Hb Lh 8#64 M G)
    (gname : MlS) (v : ValueHOL 64) (hn : ofString "heap_ptr" ≠ gname) : BL Wb Hb Lh 8#64 M (G.update (gname,v)) :=
  bl_frame h (fun _ _ => rfl) (fun H hH => ⟨H,by unfold HeapIs at *; rw [lookup_update_ne' _ _ hn]; exact hH,le_refl _⟩)

/-- The actual remainder `ptRest134` of `process_transaction` from the suffix state at `del`. -/
theorem ptRest134_aqgd {QM : Mem → GA → Prop} (Ix L40 L72 Hb Nj Nl Lp : BitVec 64)
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
    (hinc : IncorpC D B w RR SP0 P0 FM G0 J C SKB Bo U Sc n c T Out ko Excl W40 W72 M0 Ix Hb L40 L72)
    (hOR : OutRecObl D B SP0 FM n c T Out ko Excl W40 W72 M0 Ix Hb L40 L72)
    (hRet : ∀ (Hg : BitVec 64) L M G, (LPS Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧
      BL2 W40 W72 Hb L40 L72 M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LDn Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR ptRest134 := by
  unfold ptRest134
  refine aqgd_conseqA (P' := fun L M G => ∃ Hg : BitVec 64, (LPS Ix L ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧
      BL2 W40 W72 Hb L40 L72 M G) (aqgd_exE (fun Hg => ?_)) ?_
  · refine ptRest_del (R := BL2 W40 W72 Hb L40 L72) Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 jfit hwJ hwP hOut
      hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0 hJE hSE hP0Hb ECH hECH
      (fun M M' G G' H H' bls hH hH' le keep => ⟨bl_frameX bls.1 hW40 hH hH' le keep,
        bl_frameX bls.2 hW72 hH hH' le keep⟩) ?_
    refine aqgd_seq (hinc Hg) (aqgd_conseq (P := fun L M G => ∃ Y : BitVec 64,
        ((LPS Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧ PZ n c T Out ko D B Excl Hb Hg M0 M G) ∧
          BL2 W40 W72 Hb L40 L72 M G ∧ OutRec SP0 FM Y M)
      (aqgd_exE (fun Y => ptRest_tail Ix Y
        (fun M G gname y hg bls => by
          have hn : ofString "heap_ptr" ≠ gname := by rcases hg with rfl | rfl <;> decide
          exact ⟨bl_gupd bls.1 _ _ hn,bl_gupd bls.2 _ _ hn⟩)
        (hRet Hg))) ?_ (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    intro L M G ⟨⟨lp,pz⟩,bls⟩
    obtain ⟨Y,ho,orc⟩ := hOR Hg L M G ⟨⟨lp,pz⟩,bls⟩
    exact ⟨Y,⟨⟨lp,ho⟩,pz⟩,bls,orc⟩
  · intro L M G _ ⟨⟨ld,pb⟩,b40,b72⟩
    obtain ⟨H,hH,_⟩ := pb.1
    exact ⟨H,⟨ld.1,pz_of_pb hAB pb hH⟩,b40,b72⟩

#print axioms ptRest134_aqgd
end ra
end InitECandidate.Runtime
