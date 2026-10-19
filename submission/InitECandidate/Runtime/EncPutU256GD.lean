import InitECandidate.Runtime.EncToBeMinGD
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.HeapReleaseCall
import InitECandidate.Runtime.HtabGrowTail
/-!
Fenced window spec of the actual `tx_put_u256` (`heap_mark`, `alloc(32)`, `u256_to_be_min`, `rlp_encode_bytes`,
`heap_release`): writes only at or above `dst` and in the temporary block at or above the heap pointer `H`, returns a
count within the fence, and restores the heap pointer to `H`. Includes `aqgd_ga` (globals-keeping callees keep the
entry globals) and specs of `heap_mark` / `heap_release`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section hg
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A globals-keeping body keeps the entry globals in its normal and returning postconditions. -/
theorem aqgd_ga {P Q : GA → Mem → GA → Prop} {body : ProgHOL 64} (hk : keepsGA goodGA body = true)
    (h : AQGD D B A w Vn P Q RR body) (G0 : GA) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ G = G0) (fun L M G => Q L M G ∧ G = G0)
      (fun v M G => RR v M G ∧ G = G0) body := by
  intro F s code dom aw sl H hH ⟨pre,hG⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have glob := evaluate_keepsGA goodGA goodGA_bodies body hk s code
  unfold GIs at hH
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    unfold GIs at hH'
    exact ⟨sl',H',hH',q,by rw [← hH',glob,hH,hG]⟩
  · obtain ⟨H',hH',rr⟩ := r v e
    unfold GIs at hH'
    exact ⟨H',hH',rr,by rw [← hH',glob,hH,hG]⟩

/-- `heap_mark()` returns the heap pointer; memory and globals unchanged. -/
theorem heapMark_spec (M0 : Mem) (G0 : GA) (H : BitVec 64) (hH : HeapIs G0 H) :
    AQGD D B A w Vn (fun _ M G => M = M0 ∧ G = G0) (fun _ _ _ => True)
      (fun v M G => v = .val (.word H) ∧ M = M0 ∧ G = G0) (sourceFunctionBody Guest.guestFn_heap_mark) := by
  rw [source_heapMark_body]
  exact aqgd_return _ (fun s v _ _ hG ⟨hM,hG0⟩ _ ev => by
    unfold GIs at hG; subst hG hG0
    unfold HeapIs at hH
    simp [EV,evalHOLExact,hH] at ev
    exact ⟨ev.symm,hM,rfl⟩)

#print axioms aqgd_ga
#print axioms heapMark_spec
end hg
theorem jws_setHeap {SP0 P0 FM J C SKB : BitVec 64} {G0 g : GA} (h : JWS SP0 P0 FM G0 J C SKB g) (m : BitVec 64)
    (lo : P0.toNat ≤ m.toNat) (hi : m.toNat ≤ 33806089496) (al : m.toNat % 8 = 0) :
    JWS SP0 P0 FM G0 J C SKB (g.update (ofString "heap_ptr",.val (.word m))) := by
  obtain ⟨⟨⟨hf,⟨sp,hsp,a1,a2⟩,_,st⟩,hj,hc⟩,hk⟩ := h
  have ne : ∀ x : MlS, x ≠ ofString "heap_ptr" →
      (g.update (ofString "heap_ptr",.val (.word m))).lookup x = g.lookup x := fun x hx => lookup_update_ne' _ _ hx
  refine ⟨⟨⟨by rw [ne _ (by decide)]; exact hf,⟨sp,by rw [ne _ (by decide)]; exact hsp,a1,a2⟩,
    ⟨m,lookup_update_eq' _ _ _,lo,hi,al⟩,fun x hx => ?_⟩,by rw [ne _ (by decide)]; exact hj,
    by rw [ne _ (by decide)]; exact hc⟩,by rw [ne _ (by decide)]; exact hk⟩
  have : x ≠ ofString "heap_ptr" := by
    intro e; subst e; revert hx; decide
  rw [ne _ this]; exact st x hx

section hr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM J C SKB : BitVec 64} {G0 : GA}

/-- `heap_release(m)` for a valid mark: the heap pointer becomes `m`, memory unchanged. -/
theorem heapRelease_spec (M0 : Mem) (Mk : BitVec 64) (lo : P0.toNat ≤ Mk.toNat) (hi : Mk.toNat ≤ 33806089496)
    (al : Mk.toNat % 8 = 0) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn
      (fun L M _ => L.lookup (ofString "m") = some (.val (.word Mk)) ∧ M = M0) (fun _ _ _ => True)
      (fun _ M G => M = M0 ∧ HeapIs G Mk) (sourceFunctionBody Guest.guestFn_heap_release) := by
  rw [source_heapRelease_body]
  refine aqgd_seq (Q := fun _ M G => M = M0 ∧ HeapIs G Mk) (aqgd_assignGlobal _ _ (fun s v aw ⟨hm,hM⟩ _ ev => ?_))
    (aqgd_return _ (fun _ _ _ _ hG pre _ _ => by unfold GIs at hG; subst hG; exact pre))
  simp [EV,evalHOLExact,hm] at ev; subst ev
  have e : (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word Mk)) s).globals =
      s.globals.update (ofString "heap_ptr",.val (.word Mk)) := by simp [setGlobalHOLFinite]
  rw [e]
  exact ⟨jws_setHeap aw Mk lo hi al,hM,lookup_update_eq' _ _ _⟩

#print axioms heapRelease_spec
end hr
def puBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "mark") ShapeHOL.one (ofString "heap_mark") [] (ProgHOL.decCall (ofString "tmp") ShapeHOL.one (ofString "alloc") [ExpHOL.const 32#64] (ProgHOL.decCall (ofString "n") ShapeHOL.one (ofString "u256_to_be_min") [ExpHOL.var VarKind.local (ofString "v"), ExpHOL.var VarKind.local (ofString "tmp")] (ProgHOL.decCall (ofString "w") ShapeHOL.one (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "tmp"), ExpHOL.var VarKind.local (ofString "n")] (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "heap_release") [ExpHOL.var VarKind.local (ofString "mark")]) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "w")))))))

theorem pu_body_eq : sourceFunctionBody Guest.guestFn_tx_put_u256 = puBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_put_u256,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem jws_heap_facts {SP0 P0 FM J C SKB H : BitVec 64} {G0 g : GA} (h : JWS SP0 P0 FM G0 J C SKB g)
    (hH : HeapIs g H) : P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0 := by
  obtain ⟨⟨⟨_,_,⟨h',hh,lo,hi,al⟩,_⟩,_⟩,_⟩ := h
  unfold HeapIs at hH; rw [hh] at hH
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hH
  subst hH; exact ⟨lo,hi,al⟩

section pu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB : BitVec 64} {G0 : GA}

set_option linter.unusedVariables false in
/-- The actual `tx_put_u256(dst, v)`: writes only at or above `dst` and in a temporary heap block at or above the
heap pointer `H` (released on return); returns `R` with `dst + R ≤ DF + 8` and the heap pointer back at `H`. -/
theorem putU256_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (Dst H Nj : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat)
    (hfit : Dst.toNat + 16 < 2 ^ 64) (hLoH : Lo.toNat ≤ H.toNat) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧ HeapIs G H ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => False) (fun r _ G => WRet DF Dst r ∧ HeapIs G H) (sourceFunctionBody Guest.guestFn_tx_put_u256) := by
  rw [pu_body_eq]; unfold puBody
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,hH,_⟩ => jws_heap_facts aw hH) ?_
  intro ⟨hP0,hcapH,hal⟩
  -- mark = heap_mark()
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      L.lookup (ofString "mark") = some (.val (.word H)) ∧ HeapIs G H ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_heap_mark_lookup (by simp)
    (fun _ M0' G0' ⟨_,hH,_⟩ => heapMark_spec M0' G0' H hH) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro L M G v M' G' ⟨hd,hH,hn⟩ ⟨ev,_,hG⟩ _
    subst ev hG
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,lookup_update_eq' _ _ _,hH,hn⟩
  -- tmp = alloc(32)
  let P2 := fun (L : GA) (G : GA) => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    L.lookup (ofString "mark") = some (.val (.word H)) ∧ L.lookup (ofString "tmp") = some (.val (.word H)) ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
    ∃ H2 : BitVec 64, HeapIs G H2 ∧ H.toNat + 32 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word 32#64)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      v = .val (.word H) ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H2 : BitVec 64, HeapIs G' H2 ∧ H.toNat + 32 ≤ H2.toNat ∧ H2.toNat ≤ 33806089496)
    (Pc := fun L _ G => P2 L G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨_,_,hH,hn⟩
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) 32#64 H M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn,H,hH,hl,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',_,ev,_,_,c1,c2,_⟩
      exact ⟨ev,hn',H',hH',by simpa using c1,c2⟩
  · intro F s values callee rs _ H' _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨hd,hm,_,_⟩ ⟨ev,hn',H2,hH2,h32,hc⟩ _
    subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,
      lookup_update_eq' _ _ _,hn',H2,hH2,h32,hc⟩
  -- n = u256_to_be_min(v, tmp): globals kept
  let P3 := fun (L : GA) (G : GA) => P2 L G ∧ ∃ Nv : BitVec 64, L.lookup (ofString "n") = some (.val (.word Nv))
  refine aqgd_decCallSpecS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (G0' : GA) (L : GA) (_ : Mem) (G : GA) =>
      L.lookup (ofString "out") = some (.val (.word H)) ∧ G = G0')
    (RRe := fun (_ : GA) (_ : Mem) (G0' : GA) (_ : ValueHOL 64) (_ : Mem) (G' : GA) => G' = G0')
    (Pc := fun L _ G => P3 L G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_u256ToBeMin_lookup (fun _ _ _ _ _ h => h.elim)
    (fun _ _ G0' _ => aqgd_conseq (aqgd_ga (keepsGA_of_installed originalRuntimeCode_u256ToBeMin_lookup (by decide))
      (toBeMin_win hF hDF Lo hLo8 hw H hLoH (by omega)) G0') (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
      (fun _ _ _ h => h.2)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ hG ⟨_,_,ht,_⟩ _ args lookup
    unfold GIs at hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht] at args
    cases hv : s.locals.lookup (ofString "v") with
    | none => simp [hv] at args
    | some vv =>
    simp [hv] at args
    subst args
    have e := callee_eq originalRuntimeCode_u256ToBeMin_lookup lookup
    exact ⟨by rw [e]; simp (config := {decide := true}),rfl⟩
  · intro L M G v M' G' ⟨hd,hm,ht,hn,H2,hH2,h32,hc⟩ hG ok
    subst hG
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ht,hn,H2,hH2,h32,hc⟩,y,lookup_update_eq' _ _ _⟩
  -- w = rlp_encode_bytes(dst, tmp, n): globals kept
  let P4 := fun (L : GA) (G : GA) => P2 L G ∧ ∃ R : BitVec 64, L.lookup (ofString "w") = some (.val (.word R)) ∧
    Dst.toNat + R.toNat ≤ DF + 8
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (G0' : GA) (L : GA) (_ : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "n") = some (.val (.word (wordOf L0 (ofString "n"))))) ∧ G = G0')
    (RRe := fun (_ : GA) (_ : Mem) (G0' : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) => WRet DF Dst r ∧ G' = G0')
    (Pc := fun L _ G => P4 L G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_rlpEncodeBytes_lookup (by simp)
    (fun L0 _ G0' _ => aqgd_conseq (aqgd_ga (keepsGA_of_installed originalRuntimeCode_rlpEncodeBytes_lookup (by decide))
      (encodeBytes_win hF hDF Lo hLo8 hw Dst (wordOf L0 (ofString "n")) hDst hfit) G0') (fun _ _ _ h => h)
      (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ hG ⟨⟨hd,_,ht,_⟩,Nv,hn⟩ _ args lookup
    unfold GIs at hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,ht,hn] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
    rw [wordOf_eq hn]
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨hd,hm,ht,hn,H2,hH2,h32,hc⟩,_⟩ ⟨⟨R,hr,hb⟩,hG⟩ _
    subst hG hr
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,by rw [lookup_update_ne' _ _ (by decide)]; exact hm,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ht,hn,H2,hH2,h32,hc⟩,R,lookup_update_eq' _ _ _,hb⟩
  -- heap_release(mark); return w
  refine aqgd_seq (Q := fun L _ G => (∃ R : BitVec 64, L.lookup (ofString "w") = some (.val (.word R)) ∧
      Dst.toNat + R.toNat ≤ DF + 8) ∧ HeapIs G H) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (_ : GA) (L : GA) (M : Mem) (_ : GA) =>
      L.lookup (ofString "m") = some (.val (.word H)) ∧ M = M0')
    (RRe := fun (_ : GA) (M0' : Mem) (_ : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ HeapIs G' H)
    _ _ _ _ _ originalRuntimeCode_heap_release_lookup (by simp)
    (fun _ M0' _ _ => aqgd_conseq (heapRelease_spec (J := J) (C := C) (SKB := SKB) M0' H hP0 hcapH hal)
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)) ?_ ?_) (aqgd_return _ ?_)
  · intro F s values callee rs _ _ _ ⟨⟨_,hm,_⟩,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hm] at args
    subst args
    have e := callee_eq originalRuntimeCode_heap_release_lookup lookup
    exact ⟨by rw [e]; simp,rfl⟩
  · intro L M G v M' G' ⟨_,hR⟩ ⟨_,hH⟩
    exact ⟨hR,hH⟩
  · intro F s v _ _ _ ⟨⟨R,hw',hb⟩,hH⟩ _ ev
    simp [EV,evalHOLExact,hw'] at ev; subst ev
    exact ⟨⟨R,rfl,hb⟩,hH⟩

#print axioms putU256_win
end pu
end InitECandidate.Runtime
