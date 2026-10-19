import InitECandidate.Runtime.AccountDecodeArena
import InitECandidate.Runtime.OriginalWsAccountLeafCode
import InitECandidate.Runtime.OriginalDecodeAccountCode
import InitECandidate.Runtime.OriginalWsGetAccountCode
import InitECandidate.Runtime.OriginalKeccakCode
import InitECandidate.Runtime.OriginalTrieLookupCode
import InitECandidate.Runtime.VmFn_heap_mark
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.PanTwoWordResultLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- A declared call whose callee body is arena-safe from entry locals satisfying `Pe`, which the caller's arguments
establish. -/
theorem aq_decCallP {P Pe Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
      AW SP0 P0 FM G0 s.globals → SL (fun _ => True) s.locals → Pe s.locals →
      (evaluateHOLFiniteState s body).2.memory w = s.memory w ∧
      (Continuing (evaluateHOLFiniteState s body).1 → AW SP0 P0 FM G0 (evaluateHOLFiniteState s body).2.globals))
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals → P s.locals →
      SL Vn s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) → Pe callee)
    (hshape : Vn name → shape = .one)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee post v, s.code = originalRuntimeCode →
      AW SP0 P0 FM G0 s.globals → SL Vn s.locals → P s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v),post) →
      shapeEqHOL (shapeOfHOLExact v) shape = true → Pc (s.locals.update (name,v)))
    (hc : AQ SP0 P0 FM G0 w Vn Pc Qc cont)
    (hq : ∀ L L', P L → Qc L' → Q (L'.resVarEq (name,L.lookup name))) :
    AQ SP0 P0 FM G0 w Vn P Q (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw,(fun e => by cases e),by simp,by simp⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have same2 : foundShape = returnShape :=
        lookupCodeHOLFinite_installed_shape state.code.lookup function parameters found found returnShape
          foundShape values callee (by rw [code]; exact installed) lookup
      subst same2
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found foundShape installed allOne found callee foundShape
        lookup'
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
          (hpe state values callee foundShape aw pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM G0 bodyPost.globals) at frame
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                have pc := hret state values callee bodyPost v code aw sl pre args lookup' bodyRun ok.1
                obtain ⟨m2,a2,n2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by intro a ha; exact dom a (meta'.2.1 ▸ ha)) (by exact frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx pc
                exact ⟨m2.trans frame.1,a2,fun e => ⟨sl_restore (n2 e).1 sl name,hq _ _ pre (n2 e).2⟩,c2,b2⟩
              · exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)



/-- An 8-aligned block at or above a watched word misses it, including the aligned words of its bytes. -/
theorem mwin_above {D w : BitVec 64} {N : Nat} (lt : w.toNat < D.toNat) (al : D.toNat % 8 = 0)
    (fit : D.toNat + N < 2^64) : ¬ MWin D N w := by
  rintro ⟨j,hj,h | h⟩
  · have : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    rw [← h] at this; omega
  · have e1 : (D + BitVec.ofNat 64 j).toNat = D.toNat + j := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    have e2 := panByteAlign_toNat64 (D + BitVec.ofNat 64 j)
    rw [e1,← h] at e2
    have : D.toNat ≤ (D.toNat + j) / 8 * 8 := by
      have := Nat.div_add_mod D.toNat 8
      have := Nat.div_le_div_right (c := 8) (Nat.le_add_right D.toNat j)
      omega
    omega

/-- `heap_release(x)` with a mark in `[P0, HEAP_END]` (8-aligned) keeps the watched word and the arena globals. -/
theorem aq_heapRelease {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (x : MlS)
    (hx : ∀ L, P L → ∃ m : BitVec 64, L.lookup x = some (.val (.word m)) ∧ P0.toNat ≤ m.toNat ∧
      m.toNat ≤ 33806089496 ∧ m.toNat % 8 = 0) :
    AQ SP0 P0 FM G0 w Vn P P (.call (some (none,none)) (ofString "heap_release") [.var .local x]) := by
  refine aq_callP (Pc := fun L => ∃ m : BitVec 64, L.lookup (ofString "m") = some (.val (.word m)) ∧
      P0.toNat ≤ m.toNat ∧ m.toNat ≤ 33806089496 ∧ m.toNat % 8 = 0) _ _ _ _ _ vmLookup_heap_release (by simp) ?_ ?_
  · intro F s code dom aw sl pc
    rw [source_heapRelease_body]
    have hs : AQ SP0 P0 FM G0 w (fun _ => True) (fun L => ∃ m : BitVec 64, L.lookup (ofString "m") =
        some (.val (.word m)) ∧ P0.toNat ≤ m.toNat ∧ m.toNat ≤ 33806089496 ∧ m.toNat % 8 = 0) (fun _ => True)
        (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) (.return (.const 0))) := by
      refine aq_seq (aq_assignHeap _ ?_) (aq_return _)
      intro F s v _ ⟨m,hm,lo,hi,al⟩ _ ev
      simp [EV,evalHOLExact,hm] at ev
      subst ev
      exact ⟨m,rfl,lo,hi,al⟩
    have h := hs F s code dom aw sl pc
    exact ⟨h.1,h.2.1⟩
  · intro F s values callee rs _ pre _ args lookup
    obtain ⟨m,hm,lo,hi,al⟩ := hx _ pre
    have av : values = [.val (.word m)] := by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hm] at args
      exact args.symm
    subst av
    rw [pan_single_word_lookup _ _ _ _ _ vmLookup_heap_release] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨m,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi,al⟩

theorem ev_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (a : ExpHOL 64) (x : ValueHOL 64)
    (ev : EV s (.load .one a) = some x) : ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [EV,evalHOLExact] at ev
  split at ev
  · split at ev
    · rename_i addr _
      simp [memLoadHOLExact] at ev
      obtain ⟨_,rfl⟩ := ev
      cases h : s.memory addr with
      | word y => exact ⟨y,rfl⟩
    · cases ev
  · cases ev

/-- The heap mark held in local `mark`. -/
def MarkH (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ m : BitVec 64, L.lookup (ofString "mark") = some (.val (.word m)) ∧ P0.toNat ≤ m.toNat ∧
    m.toNat ≤ 33806089496 ∧ m.toNat % 8 = 0

/-- After `h = alloc(32)`: the hash block is a fresh 8-aligned block at or above `P0`, below `HEAP_END`. -/
def LeafH (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  MarkH P0 L ∧ ∃ hv : BitVec 64, L.lookup (ofString "h") = some (.val (.word hv)) ∧ P0.toNat ≤ hv.toNat ∧
    hv.toNat + 32 ≤ 33806089496 ∧ hv.toNat % 8 = 0

theorem markH_update {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : MarkH P0 L) (x : MlS) (v : ValueHOL 64)
    (hx : x ≠ ofString "mark") : MarkH P0 (L.update (x,v)) := by
  obtain ⟨m,hm,a,b,c⟩ := h
  exact ⟨m,by simp [HolFiniteMapExact.lookup_update,FUPDATE,hm]; exact fun e => absurd e hx,a,b,c⟩

/-- Keccak entry: the input word count is short and the 32-byte output block misses the watched word. -/
def KeccakPre (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ Pp N O : BitVec 64, L.lookup (ofString "p") = some (.val (.word Pp)) ∧
    L.lookup (ofString "n") = some (.val (.word N)) ∧ N.toNat < 136 ∧
    L.lookup (ofString "out") = some (.val (.word O)) ∧ ¬ MWin O 32 w

set_option maxHeartbeats 2000000 in
/-- `ws_account_leaf` keeps every word below `P0` and outside the Keccak state/pad buffers and the trie-walk nibble
scratch in every outcome (MPT errors and allocator traps included), and keeps the arena globals on continuing
outcomes; the hash block is a fresh heap block that is released before return. -/
theorem wsAccountLeaf_aq (K Pd NB : BitVec 64) (hp : w.toNat < P0.toNat)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w)
    (oN : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j)) :
    AQ SP0 P0 FM G0 w (fun x => x ≠ ofString "r") (fun _ => True) (fun _ => True)
      (sourceFunctionBody Guest.guestFn_ws_account_leaf) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ws_account_leaf,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  -- mark = heap_mark()
  refine aq_decCall (Pc := MarkH P0) (Qc := fun _ => True) _ _ _ _ _ _ _ vmLookup_heap_mark (by simp)
    (acallee_of_aq (Vn' := fun _ => True) (Q := fun _ => True) (by rw [source_heapMark_body]; exact aq_return _))
    (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v _ aw _ _ _ _ run _
    obtain ⟨_,_,⟨hpv,hhp,lo,hi,al⟩,_⟩ := aw
    rw [source_heapMark_body,evaluateHOLFiniteState_return] at run
    have ev : EV (callEntryStateHOLFinite s callee) (.var .global (ofString "heap_ptr")) =
        some (.val (.word hpv)) := by
      simp [EV,evalHOLExact,callEntryStateHOLFinite,hhp]
    simp only [EV] at ev
    rw [ev] at run
    dsimp only at run
    split at run
    · obtain ⟨e1,_⟩ := Prod.mk.inj run
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e1
      subst e1
      exact ⟨hpv,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi,al⟩
    · cases (Prod.mk.inj run).1
  -- h = alloc(32)
  refine aq_decCall (Pc := LeafH P0) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup
    (by simp) alloc_acallee (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v code aw _ pre args lookup run _
    obtain ⟨_,_,⟨hpv,hhp,lo,hi,al⟩,_⟩ := aw
    have av : values = [.val (.word 32)] := by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact] at args
      exact args.symm
    subst av
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    obtain ⟨req,_,ew,_⟩ := alloc_body_returned (callEntryStateHOLFinite s _) post hpv 32 code hhp
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) v run
    subst ew
    have sum := allocationGuard_sum_bound hpv 32 hi req
    exact ⟨markH_update pre _ _ (by decide),hpv,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,
      by simpa using sum,al⟩
  -- keccak256(addr, 20, h)
  refine aq_seq (Q := LeafH P0) (aq_callP (Pc := KeccakPre w) _ _ _ _ _ originalRuntimeCode_keccak_lookup (by simp)
    ?_ ?_) ?_
  · intro F s code _ aw _ ⟨Pp,N,O,hpp,hn,short,ho,oO⟩
    obtain ⟨eK,_⟩ := aw.2.2.2 (ofString "keccak_st") (by decide)
    obtain ⟨ePd,_⟩ := aw.2.2.2 (ofString "keccak_pad") (by decide)
    refine ⟨keccak_short_body_window s Pp N O K Pd w code hpp hn ho (eK.trans hK0) (ePd.trans hPd0) short oK oP oO,
      fun _ => ?_⟩
    rw [keccak_body_globals_frame s code]
    exact aw
  · intro F s values callee rs _ ⟨_,hv,hh,lo,fit,al⟩ sl args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    cases ha : s.locals.lookup (ofString "addr") with
    | none => simp [evalListHOLExact,evalHOLExact,ha] at args
    | some av =>
      obtain ⟨x,rfl⟩ := sl _ (by decide) av ha
      simp [evalListHOLExact,evalHOLExact,ha,hh] at args
      subst args
      rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        originalRuntimeCode_keccak_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨x,20,hv,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],by decide,
        by simp [HolFiniteMapExact.lookup_update,FUPDATE],mwin_above (by omega) al (by omega)⟩
  -- r = trie_lookup(lds (ws + 24), h)
  refine aq_decCallP (Pe := fun L => ∃ H : BitVec 64, L.lookup (ofString "key_hash32") = some (.val (.word H)))
    (Pc := MarkH P0) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_trieLookup_lookup (by simp) ?_ ?_
    (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s code _ aw _ ⟨H,hH⟩
    obtain ⟨eN,_⟩ := aw.2.2.2 (ofString "mpt_nib_scratch") (by decide)
    obtain ⟨m,g⟩ := trieLookup_body_window s H NB w code hH (eN.trans hNB0) oN
    exact ⟨m,fun _ => by rw [g]; exact aw⟩
  · intro F s values callee rs _ ⟨_,hv,hh,_⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    cases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ws"),.const 24#64])) with
    | none => simp [evalListHOLExact,hx] at args
    | some x =>
      obtain ⟨y,rfl⟩ := ev_load_one_word s _ x hx
      simp only [evalListHOLExact] at args
      rw [hx] at args
      simp [evalListHOLExact,evalHOLExact,hh] at args
      subst args
      rw [pan_two_word_result_lookup _ _ _ _ _ _ _ _ (by decide) originalRuntimeCode_trieLookup_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨hv,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩
  · intro F s _ _ _ v _ _ _ pre _ _ _ _
    exact markH_update pre.1 _ _ (by decide)
  exact aq_seq (aq_heapRelease _ (fun L h => h)) (aq_return _)

/-- A successful lookup of a three-word-parameter function binds three words. -/
theorem lookup3_words (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (f n1 n2 n3 : MlS)
    (b : ProgHOL 64) (r : ShapeHOL) (x1 x2 x3 : ValueHOL 64) (found : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hcode : code f = some ([(n1,.one),(n2,.one),(n3,.one)],b,r))
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite code f [x1,x2,x3] = some (found,callee,rs)) :
    ∃ a1 a2 a3 : BitVec 64, x1 = .val (.word a1) ∧ x2 = .val (.word a2) ∧ x3 = .val (.word a3) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i _ _ _ hl
    unfold lookupCodeHOLExact at hl
    rw [hcode] at hl
    dsimp only at hl
    split at hl
    · rename_i hcond
      have hall := hcond.2.2
      simp only [List.map_cons,List.map_nil,List.zip_cons_cons,List.zip_nil_left,List.all_cons,List.all_nil,
        Bool.and_true,Bool.and_eq_true] at hall
      obtain ⟨h1,h2,h3⟩ := hall
      obtain ⟨a1,rfl⟩ := scalar_of_shape h1
      obtain ⟨a2,rfl⟩ := scalar_of_shape h2
      obtain ⟨a3,rfl⟩ := scalar_of_shape h3
      exact ⟨a1,a2,a3,rfl,rfl,rfl⟩
    · cases hl

/-- After `a = alloc(56)`: the account record is a fresh block at or above `P0`, below `HEAP_END`. -/
def AccA (P0 : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ A : BitVec 64, L.lookup (ofString "a") = some (.val (.word A)) ∧ P0.toNat ≤ A.toNat ∧ A.toNat + 56 ≤ 33806089496

set_option maxHeartbeats 2000000 in
/-- `ws_get_account_optional` keeps every word below `P0`, outside the scratch arena, the Keccak buffers and the
nibble scratch, in every outcome (MPT/RLP errors, allocator traps), and keeps the arena globals on continuing
outcomes: the leaf lookup releases its hash block, and the decoded account is a fresh heap record. -/
theorem wsGetAccount_aq (K Pd NB : BitVec 64) (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat)
    (hp : w.toNat < P0.toNat)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w)
    (oN : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j)) :
    AQ SP0 P0 FM G0 w (fun x => x ≠ ofString "leaf") (fun _ => True) (fun _ => True)
      (sourceFunctionBody Guest.guestFn_ws_get_account_optional) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_ws_get_account_optional,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aq_decCall (Pc := fun _ => True) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_wsAccountLeaf_lookup
    (by simp) (acallee_of_aq (wsAccountLeaf_aq K Pd NB hp hK0 hPd0 hNB0 oK oP oN)) (fun h => absurd rfl h)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ (fun _ _ _ _ => trivial)
  refine aq_seq (aq_ite (CT := fun _ => True) (CF := fun _ => True) _
    (fun _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aq_return _) (aq_conseq aq_skip (fun _ h => h)
      (fun _ _ => trivial))) ?_
  refine aq_decCall (Pc := AccA P0) (Qc := fun _ => True) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup
    (by simp) alloc_acallee (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v code aw _ _ args lookup run _
    obtain ⟨_,_,⟨hpv,hhp,lo,hi,_⟩,_⟩ := aw
    have av : values = [.val (.word 56)] := by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact] at args
      exact args.symm
    subst av
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    obtain ⟨req,_,ew,_⟩ := alloc_body_returned (callEntryStateHOLFinite s _) post hpv 56 code hhp
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) v run
    subst ew
    have sum := allocationGuard_sum_bound hpv 56 hi req
    exact ⟨hpv,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,by simpa using sum⟩
  refine aq_seq (aq_callP (Pc := AcctOut w) _ _ _ _ _ originalRuntimeCode_decodeAccount_lookup (by simp) ?_ ?_)
    (aq_return _)
  · intro F s code dom aw sl pc
    have h := decodeAcct_aq hw hp F s code dom aw (sl_mono sl (fun _ _ => trivial)) pc
    exact ⟨h.1,h.2.1⟩
  · intro F s values callee rs _ ⟨A,hA,lo,fit⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.rfield 1 (.var .local (ofString "leaf"))) with
    | none => simp [evalListHOLExact,h1] at args
    | some x1 =>
      cases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.rfield 2 (.var .local (ofString "leaf"))) with
      | none => simp [evalListHOLExact,h1,h2] at args
      | some x2 =>
        simp only [evalListHOLExact] at args
        rw [h1,h2] at args
        simp [evalListHOLExact,evalHOLExact,hA] at args
        subst args
        obtain ⟨a1,a2,a3,rfl,rfl,e3⟩ := lookup3_words _ _ _ _ _ _ _ _ _ _ _ _ _
          originalRuntimeCode_decodeAccount_lookup lookup
        cases e3
        rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
          originalRuntimeCode_decodeAccount_lookup] at lookup
        simp only [Option.some.injEq,Prod.mk.injEq] at lookup
        obtain ⟨_,rfl,_⟩ := lookup
        exact ⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE],by omega,Or.inl (by omega)⟩

#print axioms aq_decCallP
#print axioms aq_heapRelease
#print axioms wsAccountLeaf_aq
#print axioms wsGetAccount_aq
end InitECandidate.Runtime
