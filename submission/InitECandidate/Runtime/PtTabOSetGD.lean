import InitECandidate.Runtime.PtStLeGD
/-!
The actual `htab_set(et, ek, ev)` call statement on an owned table (`TabO O Td H`) at the heap pointer `H`: the
table is owned by `O ∪ [H, H')` at the exit heap `H'`, memory below `H` outside `O` unchanged, the journal counter
kept; on the full arena with the block-access-list globals.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section tos
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- Exit of a set on an owned table. -/
def TOPost (O : BitVec 64 → Prop) (Td H Nj : BitVec 64) (M1 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G H' ∧ H.toNat ≤ H'.toNat ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
    TabO (fun x => O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) Td H' M ∧
    ∀ x, ¬ O x → x.toNat < H.toNat → M x = M1 x

theorem aqgd_call_htabSet_oJ {LP : GA → Prop} (et ek ev : ExpHOL 64) (Td K V H Nj : BitVec 64)
    (O : BitVec 64 → Prop) (M1 : Mem) (G1 : GA) (tob : TabO O Td H M1) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hwO : ¬ O w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] =
        some [.val (.word Td),.val (.word K),.val (.word V)]) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ TOPost O Td H Nj M1 M G) RR
      (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) := by
  obtain ⟨l,lay,hd,ho,li⟩ := tob
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => LK (irP0 Td K V) L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost Td (Canon Td l.C l.SD l.KS l.VS l.US l.OS l.OPS H) M0' l.C l.SD l.KS
        l.VS l.US l.OS l.OPS H M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst hM hG
    have hwk : ¬ Foot H Td (Canon Td l.C l.SD l.KS l.VS l.US l.OS l.OPS H) w := fun hc => by
      unfold Foot at hc
      rcases hc with ⟨lo,hi⟩ | h | h
      · exact hwO (ho w lo hi)
      · exact hwO (li w h)
      · omega
    exact aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
        originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
        (aqmh_rebound (set_aqmh (P0 := H) Td K V _ l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS l.b lay M0' hwk H
          (le_refl _)) p0)))
        (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide)))
      (fun L M G ⟨hk,hM,hG⟩ => by rw [hM,hG]; exact ⟨hn1,H,hH1,le_refl _,hk,hd,rfl,rfl⟩)
      (fun _ _ _ _ => trivial) (fun v M' G' ⟨hn',H',hH',post⟩ => ⟨hn',H',hH',post⟩)
  · intro F s values callee rs _ G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨hn',H',hH',post⟩
    subst hM hG
    obtain ⟨t',le',fr'⟩ := tabO_set ho li post
    exact ⟨lp,H',hH',le',hn',t',fun x hx hlt => fr' x hx hlt⟩

#print axioms aqgd_call_htabSet_oJ

/-- `aqgd_call_htabSet_oJ` on the full arena, carrying the block-access-list globals. -/
theorem aqgd_call_htabSet_o (bk : BalKeep) (BA IA IS KB Ix : BitVec 64) {LP : GA → Prop} (et ek ev : ExpHOL 64)
    (Td K V H Nj : BitVec 64) (O : BitVec 64 → Prop) (M1 : Mem) (G1 : GA) (tob : TabO O Td H M1)
    (hH1 : HeapIs G1 H) (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hB1 : BalG BA IA IS KB Ix G1) (hwO : ¬ O w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] =
        some [.val (.word Td),.val (.word K),.val (.word V)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => (LP L ∧ TOPost O Td H Nj M1 M G) ∧ BalG BA IA IS KB Ix G) RR
      (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) :=
  aqgd_conseq (aqgd_keepBal bk (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_call_htabSet_oJ (RR := RR) et ek ev Td K V H Nj O M1 G1 tob hH1
        hn1 hwO hwP p0 hargs) (by simp only [keepsG]; decide) (by simp only [keepsG]; decide)
        (by simp only [keepsG]; decide)))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact hB1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h.1)

#print axioms aqgd_call_htabSet_o
end tos
end InitECandidate.Runtime
