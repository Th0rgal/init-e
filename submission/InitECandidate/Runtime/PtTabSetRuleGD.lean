import InitECandidate.Runtime.PtReadyXGD
import InitECandidate.Runtime.PtPGStepGD
/-!
The actual `htab_set(t, k, v)` call on a block-object table with a values invariant (`TabRV`), under the arena
`JWSBUS`: arguments evaluate (at any state with the call-site locals, memory, globals and domain) to the table `T`, a
key `Kk` (aligned, of a supported length) and a value `V ∈ S`. A normal return keeps the caller locals and
`journal_n`, moves the heap pointer up from `Hc`, changes memory only in the table's physical region or at/above `Hc`,
and leaves a ready table at `T` with values in `S` at the exit heap pointer (root's all-plans contract).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cs
variable {D : BitVec 64 → Prop} {B : Bool} {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64}
  {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

/-- Spec-based calls whose entry premise also sees the memory domain. -/
theorem aqgd_callSpecD {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals → s.memaddrs = D →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hq : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q L M' H') :
    AQGD D B A w Vn P Q RR (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw dom.2.1 H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,H',hH',hq _ _ _ _ _ _ pre rr⟩,
                (fun v e => by cases e),by simp,by simp⟩)
            | exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqgd_callSpecD
end cs

/-- The canonical footprint at `H` of a table with layout `l` is its physical region or the heap at/above `H`. -/
theorem canon_tabPhys {T H x : BitVec 64} {l : TLay} (h : Canon T l.C l.SD l.KS l.VS l.US l.OS l.OPS H x) :
    TabPhys T l x ∨ H.toNat ≤ x.toNat := by
  unfold TabPhys InTabF
  rcases h with h | (h | h | h | h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr h

section ts
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- Frame part: the actual `htab_set` on a `TabRV` table changes memory only in its physical region or at/above the
entry heap pointer `Hc`. -/
theorem aqgd_call_htabSet_frame {LP : GA → Prop} (et ek ev : ExpHOL 64) (T Kk V Hl Hc Nj : BitVec 64) (l : TLay)
    (S : Set (BitVec 64)) (M1 : Mem) (G1 : GA)
    (hwP : w.toNat < P0.toNat) (hwT : ¬ TabPhys T l w) (rv : TabRV D B T l Hl S M1) (hH1 : HeapIs G1 Hc)
    (hN1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hHl : Hl.toNat ≤ Hc.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] =
        some [.val (.word T),.val (.word Kk),.val (.word V)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ ∃ Hp : BitVec 64, HeapIs G Hp ∧ Hc.toNat ≤ Hp.toNat ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∀ x, ¬ TabPhys T l x → x.toNat < Hc.toNat → M x = M1 x) RR
      (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) := by
  obtain ⟨F0,s0,Pt,hm,_,_,_,hP,_,hT,rd,_⟩ := rv
  refine aqgd_callSpecD (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) => LK (irP0 T Kk V) L ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (_ : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        SetPost T (Canon T l.C l.SD l.KS l.VS l.US l.OS l.OPS Hc) M0' l.C l.SD l.KS l.VS l.US l.OS l.OPS Hc M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ Hc.toNat ∧ Hc.toNat ≤ 33806089496 ∧ Hc.toNat % 8 = 0)
      (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact jws_heap_facts aw.1.1.1 hH1) ?_
    intro ⟨hP0,hHE,al⟩
    let r : PanSemStateFiniteExact 64 F0 := {s0 with globals := G1}
    have rd' := rd.transferX (r := r) rfl rfl rfl rfl hH1 (by have := rd.live.frontier.allocated; omega) hHE al
    obtain ⟨lay,hd,_⟩ := ready_hlay rd' hT
    have hwF : ¬ Foot Hc T (Canon T l.C l.SD l.KS l.VS l.US l.OS l.OPS Hc) w := fun hc => by
      rcases canon_tabPhys hc with h | h
      · exact hwT h
      · omega
    refine aqgd_conseq (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J)
      (C := C) (N := Nj) originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_lower hP0 (set_aqmh (SP0 := SP0) (FM := FM) (G0 := G0) (P0 := Hc) T Kk V _ l.KL l.SD l.C l.N l.KS l.VS
        l.US l.OS l.OPS l.b lay M1 hwF Hc (le_refl _)))))
      (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_hashSet_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨lk,hM,hG⟩
      rw [hM,hG]
      exact ⟨hN1,Hc,hH1,⟨lk,by rw [← hm]; exact hd,rfl,rfl⟩,rfl⟩
    · intro v M' G' h; exact h
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_hashSet_lookup lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨hn',H',hH',post⟩
    refine ⟨lp,H',hH',post.1,hn',fun x hx hlt => ?_⟩
    rw [← hM]
    exact post.2.1 x (fun hc => by
      rcases canon_tabPhys hc with h | h
      · exact hx h
      · omega)

#print axioms aqgd_call_htabSet_frame

/-- The actual `htab_set(t, k, v)` on a `TabRV` table: the frame part and a ready table with values in `S` at the
exit heap pointer. -/
theorem aqgd_call_htabSet_rv {LP : GA → Prop} (et ek ev : ExpHOL 64) (T Kk V Hl Hc Nj : BitVec 64) (l : TLay)
    (S : Set (BitVec 64)) (M1 : Mem) (G1 : GA)
    (hwP : w.toNat < P0.toNat) (hwT : ¬ TabPhys T l w) (rv : TabRV D B T l Hl S M1) (hH1 : HeapIs G1 Hc)
    (hN1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hHl : Hl.toNat ≤ Hc.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (sd : l.SD.toNat ≤ 56) (hV : V ∈ S)
    (hK : Kk.toNat % 8 = 0) (hKE : Kk.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek,ev] =
        some [.val (.word T),.val (.word Kk),.val (.word V)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => (LP L ∧ ∃ Hp : BitVec 64, HeapIs G Hp ∧ Hc.toNat ≤ Hp.toNat ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∀ x, ¬ TabPhys T l x → x.toNat < Hc.toNat → M x = M1 x) ∧
        ∃ (l' : TLay) (Hp : BitVec 64), G.lookup (ofString "heap_ptr") = some (.val (.word Hp)) ∧
          TabRV D B T l' Hp S M) RR
      (.call (some (none,none)) (ofString "htab_set") [et,ek,ev]) := by
  refine aqgd_addNormal (aqgd_call_htabSet_frame et ek ev T Kk V Hl Hc Nj l S M1 G1 hwP hwT rv hH1 hN1 hHl hargs) ?_
  intro F s code dom aw _ ⟨lp,hM,hG⟩ post run
  have hH : HeapIs s.globals Hc := by rw [hG]; exact hH1
  have hf := jws_heap_facts aw.1.1.1 hH
  exact setRV_post s post T Kk V Hc Hl l S et ek ev dom.2.1 dom.2.2 code Dall (by rw [hM]; exact rv) hH hHl hf.2.1
    hf.2.2 sup sd hV hK hKE (hargs (liftClock s (2 ^ 74)) dom.2.1 hM hG lp) run

#print axioms aqgd_call_htabSet_rv
end ts
end InitECandidate.Runtime
