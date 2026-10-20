import InitECandidate.Runtime.PtSufBGD
import InitECandidate.Runtime.PtSufAOGD
/-!
PtSufBGD with the interpreter output record pointer `out = Y` threaded (`LPSo`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ef
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat} {Y : BitVec 64}

end ef

section cs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}

end cs

section sb
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem} {Y : BitVec 64}

/-- `LPSo Y` with a two-word `rc`. -/
def LPRO (Y : BitVec 64) (Ix : BitVec 64) (L : GA) : Prop :=
  LPSo Y Ix L ∧ ∃ a b : BitVec 64, L.lookup (ofString "rc") = some (.rStruct [.val (.word a),.val (.word b)])

/-- Spine drops 118-125 of the actual `process_transaction`: logs list, success flag, the receipt, and its two
words stored into the block receipt array cell `lds (bo + 32) + index * 16` (outside words in `Excl`). -/
theorem ptSufBO {QM : Mem → GA → Prop} (Ix Rarr : BitVec 64)
    (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x) (hOut : Out w)
    -- the block receipt array cell: `bo + 32` holds `Rarr` (kept outside word), the two written words are in `Excl`
    (hBoD : D (Bo + 32)) (hBoO : Out (Bo + 32)) (hBoE : ¬ Excl (Bo + 32)) (hRarr : M0 (Bo + 32) = .word Rarr)
    (hO0 : Out (Rarr + Ix * 16) ∧ ∀ i, Rarr + Ix * 16 ≠ c i) (hE0 : Excl (Rarr + Ix * 16)) (hw0 : w ≠ Rarr + Ix * 16)
    (hO8 : Out (Rarr + Ix * 16 + 8) ∧ ∀ i, Rarr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Rarr + Ix * 16 + 8))
    (hw8 : w ≠ Rarr + Ix * 16 + 8) {cont : ProgHOL 64}
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (.seq .skip
        (.dec (ofString "logs") .one (.load .one (.op .add [(.var .local (ofString "out")),(.const 16)]))
        (.seq (.ite (.cmp .equal (.var .local (ofString "logs")) (.const 0)) (.call (some ((some (.local,ofString "logs")),none)) (ofString "lst_new") [(.const 8),(.const 1)]) .skip)
        (.dec (ofString "succeeded") .one (.const 1)
        (.seq (.ite (.cmp .notEqual (.load .one (.op .add [(.var .local (ofString "out")),(.const 32)])) (.const 0)) (.assign .local (ofString "succeeded") (.const 0)) .skip)
        (.decCall (ofString "rc") (.comb [.one,.one]) (ofString "encode_receipt") [(.load .one (.op .add [(.var .local (ofString "tx")),(.const 0)])),(.var .local (ofString "succeeded")),(.load .one (.op .add [(.var .global (ofString "bo")),(.const 16)])),(.var .local (ofString "logs"))]
        (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 32)])),(.panop .mul [(.var .local (ofString "index")),(.const 16)])]) (.rfield 0 (.var .local (ofString "rc"))))
        (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")),(.const 32)])),(.panop .mul [(.var .local (ofString "index")),(.const 16)]),(.const 8)]) (.rfield 1 (.var .local (ofString "rc"))))
        cont)))))))) := by
  have arr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc s.globals → DomD D B s →
      PXR n c T Out ko D B Excl H0 M0 s.memory s.globals →
      s.globals.lookup (ofString "bo") = some (.val (.word Bo)) ∧ s.memaddrs (Bo + 32) ∧ s.memory (Bo + 32) = .word Rarr :=
    fun s aw dom ⟨_,_,_,_,_,_,fr⟩ => ⟨aw.1.1.2,dom.2.1 ▸ hBoD,(fr _ hBoO hBoE).trans hRarr⟩
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_callAssign_lstNew_pxr (LP := LPSo Y Ix) _ _ _ hOut (fun h => h)
    (fun L v lp => lpso_upd lp _ v (by decide) (by decide))) aqgd_skip) ?_
  refine aqgd_dec_lpso _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_iteT _ (aqgd_assignLocal _ _ (fun s v _ _ pre _ _ =>
    ⟨lpso_upd pre.1 _ v (by decide) (by decide),pre.2⟩)) aqgd_skip) ?_
  refine aqgd_decCall_encReceipt_pxr (LP' := LPRO Y Ix) _ _ _ _ _ hF hDF hcap K Pd NB hK0 hPd0 safe hOutSafe hkoWs hOut
    (fun L v lp ⟨a,b,hv⟩ => ⟨lpso_upd lp _ v (by decide) (by decide),a,b,by subst hv; exact lookup_update_eq' _ _ _⟩)
    ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_store_exclS (LP := LPRO Y Ix) _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw0 hO0 hE0) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 32#64) := hd
    have hm' : s.memory (Bo + 32#64) = .word Rarr := hm
    have hi := lp.1.1.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨a,ev.symm⟩
  refine aqgd_seq (aqgd_store_exclS (LP := LPRO Y Ix) _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw8 hO8 hE8) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 32#64) := hd
    have hm' : s.memory (Bo + 32#64) = .word Rarr := hm
    have hi := lp.1.1.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL,BitVec.add_assoc]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨b,ev.symm⟩
  exact aqgd_conseq hcont (fun _ _ _ h => ⟨h.1.1,h.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSufBO
end sb
end InitECandidate.Runtime
