import InitECandidate.Runtime.PtGenCallGD
import InitECandidate.Runtime.HashNewReady
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.HashNewZero
import InitECandidate.Runtime.HashNewFrontierFacts
import InitECandidate.Runtime.HashNewReadySafePlan
import InitECandidate.Runtime.HashNewHeapDomainsSafePlan
import InitECandidate.Runtime.HashNewCallUnsafeTerminal
import InitECandidate.Runtime.HashNewBodySafePlan
/-!
A fresh `htab_new` table is a ready table with no values (`TabRV … ∅`): a returned run of the actual `htab_new` body
from an entry state with the call's exact locals is the body run of a caller call (one more clock tick), so root's
call-level readiness (`evaluate_htabNew_ready`, clock-lifted) applies to its exit memory.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed handler-free call leaves the memory of its body run. -/
theorem call_normal_body_memory {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 = none) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.memory = post.memory := by
  rw [evaluateHOLFiniteState_call,args] at success ⊢
  dsimp only at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  rw [if_neg clock,run] at success ⊢
  cases result with
  | none => cases success
  | some result =>
    cases result with
    | returned value =>
      dsimp only at success ⊢
      split at success
      · rename_i goodShape
        simp only [goodShape,if_true]
      · cases success
    | _ => cases success

#print axioms call_normal_body_memory

/-- The layout of a fresh `htab_new(KL, Cp)` table at `Hc`. -/
def newLay (Hc KL Cp : BitVec 64) (b : Nat) : TLay :=
  ⟨KL,allocationEnd 0 KL,Cp,0,allocationEnd Hc 72,htabNewValues Hc KL Cp,htabNewUsed Hc KL Cp,htabNewOrder Hc KL Cp,
    htabNewOrderPos Hc KL Cp,b⟩

/-- A returned run of the actual `htab_new` body from the call's exact locals at heap pointer `Hc` leaves a ready
table at `Hc` with no values. -/
theorem newRV_ret {F : Type} {D : BitVec 64 → Prop} {B : Bool} (s post : PanSemStateFiniteExact 64 F)
    (KL Cp Hc : BitVec 64) (b : Nat) (v : ValueHOL 64)
    (hloc : s.locals = (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word KL))).update
      (ofString "cap",.val (.word Cp)))
    (hd : s.memaddrs = D) (hb : s.be = B) (code : s.code = originalRuntimeCode)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc))) (al : Hc.toNat % 8 = 0)
    (hHE : Hc.toNat ≤ 33806089496) (power : Cp.toNat = 2 ^ b) (kb : KL.toNat ≤ 52)
    (hC : 1 < Cp.toNat)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_new) = (some (.returned v),post)) :
    v = .val (.word Hc) ∧
      TabRV D B Hc (newLay Hc KL Cp b) (allocationEnd (htabNewOrderPos Hc KL Cp) (Cp * 8)) ∅ post.memory := by
  let k : Nat := Cp.toNat + 8
  let s2 : PanSemStateFiniteExact 64 F := liftClock s k
  have lift := panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_htab_new) s _ post k ⟨run,by simp⟩
  let r : PanSemStateFiniteExact 64 F := {s2 with clock := s2.clock + 1, locals := HolFiniteMapExact.empty}
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word KL))).update (ofString "cap",.val (.word Cp))
  have entry : callEntryStateHOLFinite r callee = s2 := by
    show { r with clock := r.clock - 1, locals := callee } = s2
    simp only [r,s2,liftClock,Nat.add_sub_cancel]
    rw [hloc]
  have args : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a)) [.const KL,.const Cp] =
      some [.val (.word KL),.val (.word Cp)] := rfl
  have dom : ∀ a : BitVec 64, a.toNat < 33806089496 → r.memaddrs a := fun a h => by
    show s.memaddrs a; rw [hd]; exact Dall a h
  by_cases safe : AllocationPlanSafe Hc (htabNewAllocationSizes KL Cp)
  swap
  · exfalso
    have kL : s2.locals.lookup (ofString "key_len") = some (.val (.word KL)) := by
      show s.locals.lookup _ = _
      rw [hloc]; simp [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
    have cL : s2.locals.lookup (ofString "cap") = some (.val (.word Cp)) := by
      show s.locals.lookup _ = _
      rw [hloc]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    have domains := htabNew_requested_heap_domains s2 Hc KL Cp hHE (fun a h => by show s.memaddrs a; rw [hd]; exact Dall a h)
    exact evaluate_htabNew_body_unsafe_no_return s2 Hc KL Cp code (by show Cp.toNat + 8 ≤ s.clock + k; omega) hH hHE kL cL
      domains.1 (fun sf => (domains.2 sf).1) (fun sf => (domains.2 sf).2) safe v (congrArg Prod.fst lift)
  have hdom := htabNew_heap_domains_of_safe_plan r Hc KL Cp hHE safe dom
  have kL : s2.locals.lookup (ofString "key_len") = some (.val (.word KL)) := by
    show s.locals.lookup _ = _
    rw [hloc]; simp [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have cL : s2.locals.lookup (ofString "cap") = some (.val (.word Cp)) := by
    show s.locals.lookup _ = _
    rw [hloc]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨_,brun,_⟩ := evaluate_source_htabNew_of_safe_plan s2 Hc KL Cp code (by show Cp.toNat + 7 ≤ s.clock + k; omega)
    hH hHE al safe kL cL hdom.2.1 hdom.2.2.1 hdom.2.2.2
  have ev : v = .val (.word Hc) := by
    have := congrArg Prod.fst lift
    have h2 := congrArg Prod.fst brun
    simp only at this h2
    rw [show (evaluateHOLFiniteState s2 (sourceFunctionBody Guest.guestFn_htab_new)).1 = some (.returned v) from this]
      at h2
    simpa using h2
  obtain ⟨ready,crun,empty,_,_,_,_,rdom,rbe,rdy,_⟩ := evaluate_htabNew_ready_of_safe_plan r (.const KL) (.const Cp) Hc KL Cp b
    args power hdom.1 code (by show Cp.toNat + 8 ≤ s.clock + k + 1; omega) hH kb al hHE safe hdom.2.1 hdom.2.2.1
    hdom.2.2.2
  have lookup : lookupCodeHOLFinite r.code.lookup (ofString "htab_new") [.val (.word KL),.val (.word Cp)] =
      some (sourceFunctionBody Guest.guestFn_htab_new,callee,.one) := by
    show lookupCodeHOLFinite s.code.lookup _ _ = _
    rw [code]; exact pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_htabNew_lookup
  have mem := call_normal_body_memory r (liftClock post k) (ofString "htab_new") _ _ _ callee _ _ args lookup
    (by show s.clock + k + 1 ≠ 0; omega) (by rw [entry]; exact lift) (by rw [crun])
  rw [crun] at mem
  have rd := rdy
  refine ⟨ev,F,ready,_,mem,rdom.trans hd,rbe.trans hb,rd.live.arrays.code,le_refl _,hC,al,rdy,?_⟩
  intro capacity used values capField usedField valuesField slot inside occupied value _
  have c16 := rd.live.arrays.cell16
  have c48 := rd.live.arrays.cell48
  rw [capField] at c16; rw [usedField] at c48
  simp only [HolWordLab.word.injEq] at c16 c48
  subst c16 c48
  exact absurd (hashOccupiedCount_zero_reads capacity _ empty slot inside) occupied

#print axioms newRV_ret

section rm
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Strengthen the return predicate with any fact (on the value and the exit memory/globals) about returned runs. -/
theorem aqgd_addReturnM {P Q : GA → Mem → GA → Prop} {X : ValueHOL 64 → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B A w Vn P Q RR p)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomD D B s → A s.globals →
      SL Vn s.locals → P s.locals s.memory s.globals → ∀ (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState s p = (some (.returned v),post) → X v post.memory post.globals) :
    AQGD D B A w Vn P Q (fun v M G => RR v M G ∧ X v M G) p := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl _ rfl pre
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',q⟩ := r v e
  refine ⟨H',hH',q,?_⟩
  unfold GIs at hH'; rw [← hH']
  exact hr s code dom aw sl pre v _ (Prod.ext e rfl)

#print axioms aqgd_addReturnM
end rm

section nr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var 1 name = htab_new(KL, Cp)` with the fresh table ready and value-free (`TabRV … ∅`). -/
theorem aqgd_decCall_htabNew_rv {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (KL Cp : BitVec 64)
    (b : Nat) {cont : ProgHOL 64} (H Nj : BitVec 64) (M1 : Mem) (G1 : GA) (hH1 : HeapIs G1 H)
    (hn1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj))) (hw : w.toNat < H.toNat)
    (power : Cp.toNat = 2 ^ b) (kb : KL.toNat ≤ 52) (hC : 1 < Cp.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hres : ∀ (L : GA) (H' : BitVec 64) (M' : Mem) (G' : GA), LP L →
      (∀ x, x.toNat < H.toNat → M' x = M1 x) → HeapIs G' H' → H.toNat + 72 ≤ H'.toNat →
      H'.toNat ≤ 33806089496 → NewTab H H' KL Cp M' →
      TabRV D B H (newLay H KL Cp b) (allocationEnd (htabNewOrderPos H KL Cp) (Cp * 8)) ∅ M' →
      G'.lookup (ofString "journal_n") = some (.val (.word Nj)) → Pc (L.update (name,.val (.word H))) M' G')
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name .one (ofString "htab_new") [.const KL,.const Cp] cont) := by
  let callee : GA :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word KL))).update (ofString "cap",.val (.word Cp))
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) => L = callee ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0' x) ∧ OnlyHeap G0' G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧
      (v = .val (.word H) ∧ TabRV D B H (newLay H KL Cp b) (allocationEnd (htabNewOrderPos H KL Cp) (Cp * 8)) ∅ M'))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hc
    (fun L M G L' M' G' ⟨lp,_,_⟩ qc => hq L L' M' G' lp qc)
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    subst M0' G0'
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G1 ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
      (fun _ _ g aw ⟨_,_,hg⟩ => by
        rw [hg] at aw; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH1).2.1,(jws_heap_facts aw.1.1.1 hH1).2.2⟩) ?_
    intro ⟨hsc,hHE,al⟩
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_htabNew_lookup
      (by decide)) (htabNew_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) (w := w) KL Cp H hw M1 G1))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_addReturnM (aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_htabNew_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabNew_lookup (by decide)) h1) ?_ (fun _ _ _ h => h.elim) ?_) ?_
    · intro L M G ⟨hl,hM',hG'⟩
      rw [hM',hG']
      refine ⟨⟨⟨⟨fun p hp => ?_,rfl,hH1⟩,rfl⟩,hsc⟩,hn1⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl <;> (rw [hl]; simp (config := {decide := true}) [callee,HolFiniteMapExact.lookup_update,FUPDATE])
    · intro v M' G' ⟨⟨rr,_⟩,hn'⟩
      exact ⟨rr,hn'⟩
    · intro F s code dom _ _ ⟨hl,hm,hg⟩ v post run
      have hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) := by rw [hg]; exact hH1
      exact newRV_ret s post KL Cp H b v hl dom.2.1 dom.2.2 code Dall hH al hHE power kb hC run
  · intro F s values callee' rs _ H' hG _ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact] at ev1 ev2; subst ev1 ev2
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_htabNew_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨rfl,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,_⟩ ⟨⟨⟨Tt,ev,hHT,fr,_,H',hH',hT,hE,nt⟩,hn'⟩,ev',rv⟩ _
    rw [ev] at ev'
    simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at ev'
    subst ev ev'
    exact hres L H' M' G' lp (fun x hx => by rw [fr x hx,hM]) hH' hT hE nt rv hn'

#print axioms aqgd_decCall_htabNew_rv
end nr
end InitECandidate.Runtime
