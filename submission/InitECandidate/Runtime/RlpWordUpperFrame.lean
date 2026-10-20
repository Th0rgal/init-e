import InitECandidate.Runtime.RlpPutBeUpperFrame
import InitECandidate.Runtime.EncWritersGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}
theorem hdrTail_upper_win (hF : Fence D DF)
    (Dst X : BitVec 64) (hfit : Dst.toNat + 16 < 2 ^ 64) (above : Dst.toNat + 9 ≤ w.toNat) (xname : MlS)
    (hxl : xname ≠ ofString "ll") (hxd : ofString "dst" ≠ xname) (e : ExpHOL 64) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup xname = some (.val (.word X)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (hdrTail xname e) := by
  unfold hdrTail
  let Pc := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup xname = some (.val (.word X)) ∧
    ∃ Lw : BitVec 64, L.lookup (ofString "ll") = some (.val (.word Lw)) ∧ Lw.toNat ≤ 8
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) => L.lookup (ofString "v") = some (.val (.word X)))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) =>
      ∃ n : BitVec 64, r = .val (.word n) ∧ n.toNat ≤ 8)
    (Pc := fun L _ _ => Pc L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpBeLen_lookup (by simp)
    (fun _ _ _ _ => by
      rw [beLenBody_eq]
      exact aqgd_conseq (beLen_spec X) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨_,hx⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hx] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpBeLen_lookup lookup
    rw [e]; simp
  · intro L _ _ r _ _ ⟨hd,hx⟩ ⟨n,hr,hn⟩ _
    subst hr
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ hxl]; exact hx,n,
      lookup_update_eq' _ _ _,hn⟩
  refine aqgd_seq (r_stb_below (LP := Pc) (LQ := fun L => Pc L ∧ Dst.toNat < DF + 8) _ _ ?_) ?_
  · intro F s _ lp
    exact ⟨Dst,by simp [EV,evalHOLExact,lp.1],(by omega),fun hD => ⟨lp,fence_byte hF hD⟩⟩
  refine aqgd_seq (Q := fun L _ _ => (Pc L ∧ Dst.toNat < DF + 8) ∧
      ((wordOf L (ofString "ll")).toNat = 0 ∨ Dst.toNat + 1 + (wordOf L (ofString "ll")).toNat ≤ DF + 8))
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
        L.lookup (ofString "dst") = some (.val (.word (Dst + 1))) ∧
          L.lookup (ofString "n") = some (.val (.word (wordOf L0 (ofString "ll")))))
      (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (_ : ValueHOL 64) (_ : Mem) (_ : GA) =>
        (wordOf L0 (ofString "ll")).toNat = 0 ∨ Dst.toNat + 1 + (wordOf L0 (ofString "ll")).toNat ≤ DF + 8)
      _ _ _ _ _ originalRuntimeCode_rlpPutBe_lookup (by simp) ?_ ?_ (fun _ _ _ _ _ _ pre rre => ⟨pre,rre⟩))
    (aqgd_return _ ?_)
  · intro L0 _ _ ⟨⟨_,_,Lw,hl,hle⟩,_⟩
    rw [wordOf_eq hl,putBeBody_eq]
    have e1 : (Dst + 1).toNat = Dst.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact aqgd_conseq (putBe_upper_win hF (Dst + 1) Lw (by omega) hle (by omega)) (fun _ _ _ h => h)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => by rw [e1] at h; omega)
  · intro F s values callee rs _ _ _ ⟨⟨hd,hx,Lw,hl,_⟩,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hx,hl,wordOpHOL,wordOp,valueIsWord,valueWord] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpPutBe_lookup lookup
    rw [wordOf_eq hl]
    refine ⟨?_,?_⟩ <;> (rw [e]; simp (config := {decide := true}))
  · intro F s v _ _ _ ⟨⟨⟨_,_,Lw,hl,hle⟩,hlt⟩,hr⟩ _ ev
    rw [wordOf_eq hl] at hr
    simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (1 + Lw).toNat = 1 + Lw.toNat := by simp [BitVec.toNat_add]; omega
    refine ⟨1 + Lw,rfl,by omega,by omega,?_⟩
    rw [e1]; omega

theorem oneByte_upper_win (hF : Fence D DF) (Dst : BitVec 64) (above : Dst.toNat < w.toNat) {LP : GA → Prop}
    (hd : ∀ L, LP L → L.lookup (ofString "dst") = some (.val (.word Dst))) (v : ExpHOL 64) {Q : GA → Mem → GA → Prop} :
    AQGD D B A w (fun _ => False) (fun L _ _ => LP L) Q (fun r _ _ => HdrRet DF Dst r)
      (.seq (.storeByte (.var .local (ofString "dst")) v) (.return (.const 1#64))) :=
  aqgd_seq (r_stb_below (LP := LP) (LQ := fun _ => Dst.toNat < DF + 8) _ _
      (fun s _ lp => ⟨Dst,by simp [EV,evalHOLExact,hd _ lp],above,fun hD => fence_byte hF hD⟩))
    (aqgd_return _ (fun _ v _ _ _ h _ ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨1,rfl,by simp,by simp,by simp; omega⟩))

theorem encodeWord_upper_win (hF : Fence D DF) (Dst W : BitVec 64)
    (hfit : Dst.toNat + 16 < 2 ^ 64) (above : Dst.toNat + 9 ≤ w.toNat) :
    AQGD D B A w (fun _ => False)
      (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ L.lookup (ofString "w") = some (.val (.word W)))
      (fun _ _ _ => False) (fun r _ _ => HdrRet DF Dst r) (sourceFunctionBody Guest.guestFn_rlp_encode_word) := by
  rw [ewBody_eq]; unfold ewBody
  exact aqgd_seq (r_ite _ (oneByte_upper_win hF Dst (by omega) (fun _ h => h.1) _) aqgd_skip)
    (aqgd_seq (r_ite _ (oneByte_upper_win hF Dst (by omega) (fun _ h => h.1) _) aqgd_skip)
      (hdrTail_upper_win hF Dst W hfit above _ (by decide) (by decide) _))

#print axioms encodeWord_upper_win
end
end InitECandidate.Runtime
