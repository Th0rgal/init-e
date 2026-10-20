import InitECandidate.Runtime.PtUBLoop2GD
/-!
The actual `update_builder_from_tx` body in the block-access-list builder world: from the builder world at entry and
the source-table validity (the accounts-written table `ts + 16`, the storage outer map `ts + 32` and its inner tables,
all with content and outside every region the builder writes), every return gives 0 and is a world step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ub
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}
  {G1 : GA}

theorem updateBuilder_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (u0 : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 G1)
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
    (hwP : w.toNat < P0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun _ M G => M = M0 ∧ G = G1) (fun _ _ _ => False)
      (fun v M G => v = .val (.word 0#64) ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (sourceFunctionBody Guest.guestFn_update_builder_from_tx) := by
  refine uw_heapFact (P := fun _ _ _ => True) u0 (fun ⟨p0,_,_⟩ => ?_) |> fun h =>
    aqgd_conseq h (fun _ _ _ hh => ⟨trivial,hh⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have hw0 : w.toNat < H0.toNat := by omega
  have st0 := ust_refl u0
  let W := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G
  have bg0 := u0.2.2.1
  rw [ubBody_eq]
  unfold ubBody
  -- idx = bal_index
  refine aqgd_decD (Pb := fun L M G => L.lookup (ofString "idx") = some (.val (.word Ix)) ∧ M = M0 ∧ G = G1)
    (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ _ _ hG ⟨_,hM,hG1⟩ _ ev _
    unfold GIs at hG
    have gi : s.globals.lookup (ofString "bal_index") = some (.val (.word Ix)) := by rw [hG,hG1]; exact bg0.2.2.2.2
    simp [EV,evalHOLExact,gi] at ev; subst ev
    exact ⟨lookup_update_eq' _ _ _,hM,hG1⟩
  -- aw = lds (ts + 16)
  refine aqgd_decD (Pb := fun L M G => LK [(ofString "aw",Taw),(ofString "idx",Ix)] L ∧ M = M0 ∧ G = G1)
    (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ aw dom hG ⟨li,hM,hG1⟩ _ ev _
    obtain ⟨eg,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "ts") (by decide)
    have ea : EV s (.op .add [.var .global (ofString "ts"),.const 16#64]) = some (.val (.word (Ts + 16#64))) := by
      simp [EV,evalHOLExact,evalListHOLExact,eg,hTs,wordOpHOL,wordOp,valueIsWord,valueWord]
    unfold EV at ev
    rw [eval_load_word s _ _ Taw ea (by rw [dom.2.1]; exact cAw.1) (by rw [hM]; exact cAw.2)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    refine ⟨fun p hp => ?_,hM,hG1⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl
    · exact lookup_update_eq' _ _ _
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact li
  -- cap = lds (aw + 24)
  obtain ⟨cellA,domA⟩ := tcont_cell24 tcA
  refine aqgd_decD (Pb := fun L M G => LK [(ofString "idx",Ix),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
      M = M0 ∧ G = G1) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ _ dom _ ⟨lk,hM,hG1⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "aw") Taw 24#64 law.N
      (by simp [evalHOLExact,lk_get lk _ _ (List.mem_cons_self)]) (by rw [dom.2.1]; exact domA)
      (by rw [hM]; exact cellA)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    refine ⟨fun p hp => ?_,hM,hG1⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact lk_get lk _ _ (by simp)
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact lk_get lk _ _ (by simp)
    · exact lookup_update_eq' _ _ _
  -- i = 0
  refine aqgd_decD (Pb := fun L M G => (LK [(ofString "idx",Ix),(ofString "aw",Taw),(ofString "cap",law.N)] L ∧
      W M G) ∧ ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ law.N.toNat)
    (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ _ _ _ ⟨lk,hM,hG1⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    refine ⟨⟨lk_update lk _ _ (by
      intro p hp; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl <;> (dsimp only; decide)),by rw [hM,hG1]; exact st0⟩,
      0#64,lookup_update_eq' _ _ _,by simp⟩
  refine aqgd_seq (aqgd_conseq (ubLoop1_aqgd bk wsr ne Bs hBs hcB ne40 Ts hTs hc40 hSkSO hSk Ix Taw law tcA klA ncA
    hAwR hwP hw0 hwk0 hwR0 hwO0 Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)) ?_
  -- outer = lds (ts + 32)
  refine aqgd_decD (Pb := fun L M G => (LK [(ofString "idx",Ix),(ofString "outer",Tout)] L ∧ W M G))
    (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ aw dom hG ⟨⟨lk,st⟩,_⟩ _ ev _
    obtain ⟨eg,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "ts") (by decide)
    have ea : EV s (.op .add [.var .global (ofString "ts"),.const 32#64]) = some (.val (.word (Ts + 32#64))) := by
      simp [EV,evalHOLExact,evalListHOLExact,eg,hTs,wordOpHOL,wordOp,valueIsWord,valueWord]
    have cell : s.memory (Ts + 32#64) = .word Tout := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fr⟩ := st
      obtain ⟨a,b,c',d⟩ := cOut.2.2
      rw [fr _ a b c' d]; exact cOut.2.1
    unfold EV at ev
    rw [eval_load_word s _ _ Tout ea (by rw [dom.2.1]; exact cOut.1) cell] at ev
    simp only [Option.some.injEq] at ev; subst ev
    refine ⟨fun p hp => ?_,st⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact lk_get lk _ _ (by simp)
    · exact lookup_update_eq' _ _ _
  -- cap = lds (outer + 24)
  refine aqgd_seq (Q := fun L M G => LK [(ofString "idx",Ix),(ofString "outer",Tout),(ofString "cap",lout.N)] L ∧
      W M G) (aqgd_assignLocal _ _ (fun s v _ dom ⟨lk,st⟩ _ ev => ?_)) ?_
  · obtain ⟨cellO,domO⟩ := tcont_cell24 (tcont_of_ust tcO ncO.le hOutR st)
    unfold EV at ev
    rw [eval_record_word s .local (ofString "outer") Tout 24#64 lout.N
      (by simp [evalHOLExact,lk_get lk (ofString "outer") Tout (by simp)]) (by rw [dom.2.1]; exact domO) cellO] at ev
    simp only [Option.some.injEq] at ev; subst ev
    refine ⟨fun p hp => ?_,st⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact lk_get lk _ _ (by simp)
    · show _ = _; rw [lookup_update_ne' _ _ (by dsimp only; decide)]; exact lk_get lk _ _ (by simp)
    · exact lookup_update_eq' _ _ _
  -- i = 0
  refine aqgd_seq (Q := fun L M G => ((LK [(ofString "idx",Ix),(ofString "outer",Tout),(ofString "cap",lout.N)] L ∧
      True) ∧ W M G) ∧ ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ lout.N.toNat)
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨lk,st⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨lk_update lk _ _ (by
      intro p hp; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl <;> (dsimp only; decide)),trivial⟩,st⟩,0#64,lookup_update_eq' _ _ _,by simp⟩
  refine aqgd_seq (aqgd_conseq (ubLoop2_aqgd bk wsr ne Bs hBs hcB Ix Tout lout tcO klO ncO hOutR hIn hwP hw0 hwk0 hwR0
    hwO0 Dall) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.elim)) ?_
  exact aqgd_return _ (fun s v _ _ hG ⟨⟨_,st⟩,_⟩ _ ev => by
    simp [EV,evalHOLExact] at ev
    unfold GIs at hG; subst hG
    exact ⟨ev.symm,st⟩)

#print axioms updateBuilder_aqgd

end ub
end InitECandidate.Runtime
