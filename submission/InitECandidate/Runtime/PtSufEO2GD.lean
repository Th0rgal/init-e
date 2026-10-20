import InitECandidate.Runtime.PtSufDO2GD
import InitECandidate.Runtime.PtSufEOGD
/-!
`ptSufD_126O` (spine drops 120-126 from the receipt state) over the arena with the `bal_*` globals pinned (`JWB`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section e2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop} {Y : BitVec 64}

  {BA IA IS KB Ixb : BitVec 64}

/-- Spine drop 126 of `process_transaction` for any continuation `rest` (from `del = lds(out + 24)` on). -/
theorem ptSufD_126O2 (bk : BalKeep2) {QM : Mem → GA → Prop} (Ix L40 L72 : BitVec 64) {rest : ProgHOL 64}
    (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hrest : ∀ Hb Nj Nl Lp : BitVec 64, H0.toNat ≤ Hb.toNat →
      AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
        (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl' Hb Nj M0 M G) ∧
          BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => LPSo Y Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (.dec (ofString "nl") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 8#64]))
        (.dec (ofString "lp") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 0#64]))
          (.seq (.assign .local (ofString "i") (.const 0#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.decCall (ofString "slot") .one (ofString "lst_push")
                  [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
                  (.seq (.store (.var .local (ofString "slot"))
                      (.load .one (.op .add [.var .local (ofString "lp"),
                        .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))))
              (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
                (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0#64))
                    (.assign .local (ofString "stable_log_cap") (.const 1#64)) .skip)
                  (.decCall (ofString "stable_logs") .one (ofString "lst_new")
                    [.const 8#64,.var .local (ofString "stable_log_cap")]
                    (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64])
                        (.var .local (ofString "nl")))
                      (.dec (ofString "stable_lp") .one
                        (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
                        (.seq (.assign .local (ofString "i") (.const 0#64))
                          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])
                                (.load .one (.op .add [.var .local (ofString "lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
                            (.decCall (ofString "rl") .one (ofString "lst_push")
                              [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                              (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
                                rest))))))))))))) := by
  refine aqgd_conseqA (P' := fun L M G => ∃ Hb Nj : BitVec 64, ((LPSo Y Ix L ∧ PB n c T Out ko D B Excl' Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ H0.toNat ≤ Hb.toNat) ?_ ?_
  · exact aqgd_exE (fun Hb => aqgd_exE (fun Nj => aqgd_pureE (fun h0 =>
      ptSufD_headO2 bk Ix L40 L72 hW40 hW72 hdis (fun x hx => (hL40.1 x hx).2.2) (fun x hx => (hL72.1 x hx).2.2) hOut
        hB40 hB72 (fun Nl Lp => hrest Hb Nj Nl Lp h0))))
  · intro L M g aw ⟨lp,px⟩
    obtain ⟨Hb,Nj,hH,h0,pb⟩ := pb_of_pxr px
    have hP0 := (jws_heap_facts aw.1.1.1.1 hH).1
    exact ⟨Hb,Nj,⟨⟨lp,pb_excl pb hsub⟩,bl_of_bl0 hL40 pb.2.2.2 hH hP0,bl_of_bl0 hL72 pb.2.2.2 hH hP0⟩,h0⟩

#print axioms ptSufD_126O2
end e2
end InitECandidate.Runtime
