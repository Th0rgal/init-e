import InitECandidate.Runtime.ArenaHoare
import InitECandidate.Runtime.OriginalRlpValidationCode
import InitECandidate.Runtime.OriginalRlpHeaderCode
import InitECandidate.Runtime.OriginalRlpValidationWrapperCode
import InitECandidate.Runtime.OriginalScratchReleaseCode
import InitECandidate.Runtime.ScratchMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- The scratch record held in `rec` lies in `[FM, SP0)`. -/
def RecIn (SP0 FM : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ q : BitVec 64, L.lookup (ofString "rec") = some (.val (.word q)) ∧ FM.toNat ≤ q.toNat ∧ q.toNat + 24 ≤ SP0.toNat

theorem scratchEnd24_bound (sp FM : BitVec 64) (hfm : FM.toNat ≤ sp.toNat) (hn : (24 : BitVec 64) ≤ sp - FM)
    (within : FM ≤ scratchAllocationEnd sp 24) :
    FM.toNat ≤ (scratchAllocationEnd sp 24).toNat ∧ (scratchAllocationEnd sp 24).toNat + 24 ≤ sp.toNat := by
  have h1 : (sp - FM).toNat = sp.toNat - FM.toNat := by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hfm)]
  have h2 : 24 ≤ (sp - FM).toNat := BitVec.le_def.mp hn
  have h3 : (sp - 24#64).toNat = sp.toNat - 24 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega))]; simp
  have h4 : (scratchAllocationEnd sp 24).toNat ≤ (sp - 24#64).toNat := by
    unfold scratchAllocationEnd; rw [BitVec.toNat_and]; exact Nat.and_le_left
  exact ⟨BitVec.le_def.mp within,by omega⟩


theorem aqRec_ofT {p : ProgHOL 64} (h : AQT SP0 P0 FM G0 w Vn p) :
    AQ SP0 P0 FM G0 w Vn (RecIn SP0 FM) (fun _ => True) p := by
  unfold AQT at h; exact aq_conseq h (fun _ _ => trivial) (fun _ h => h)

theorem aqRec_storeSeq (d v : ExpHOL 64) {rest : ProgHOL 64}
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → RecIn SP0 FM s.locals →
      SL Vn s.locals → ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ w ≠ a)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, AW SP0 P0 FM G0 s.globals → RecIn SP0 FM s.locals →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y))
    (hr : AQ SP0 P0 FM G0 w Vn (RecIn SP0 FM) (fun _ => True) rest) :
    AQ SP0 P0 FM G0 w Vn (RecIn SP0 FM) (fun _ => True) (.seq (.store d v) rest) :=
  aq_seq (aq_store d v hd hv) hr

theorem rec_addr (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (k : BitVec 64) (hk : k.toNat < 24) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → RecIn SP0 FM s.locals →
      SL Vn s.locals → ∃ a : BitVec 64,
        EV s (.op .add [.var .local (ofString "rec"),.const k]) = some (.val (.word a)) ∧ w ≠ a := by
  intro F s _ ⟨q,hq,lo,hi⟩ _
  refine ⟨q + k,?_,?_⟩
  · simp [EV,evalHOLExact,evalListHOLExact,hq,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro e
    have : (q + k).toNat = q.toNat + k.toNat := by rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
    rw [← e] at this
    omega

theorem rec_addr0 (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → RecIn SP0 FM s.locals →
      SL Vn s.locals → ∃ a : BitVec 64, EV s (.var .local (ofString "rec")) = some (.val (.word a)) ∧ w ≠ a := by
  intro F s _ ⟨q,hq,lo,hi⟩ _
  refine ⟨q,?_,?_⟩
  · simp [EV,evalHOLExact,hq]
  · intro e; subst e; omega

theorem sl_varV (x : MlS) (hx : Vn x) {R : HolFiniteMapExact MlS (ValueHOL 64) → Prop} :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, AW SP0 P0 FM G0 s.globals → R s.locals → SL Vn s.locals →
      EV s (.var .local x) = some v → ∃ y : BitVec 64, v = .val (.word y) := by
  intro F s v _ _ sl ev
  simp [EV,evalHOLExact] at ev
  exact sl x hx v ev

/-- The `rec = scratch_alloc(24)` declaration: its continuation starts with a record in `[FM, SP0)`. -/
theorem aqT_scratchRec {cont : ProgHOL 64}
    (hc : AQ SP0 P0 FM G0 w Vn (RecIn SP0 FM) (fun _ => True) cont) :
    AQT SP0 P0 FM G0 w Vn (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24] cont) := by
  unfold AQT
  refine aq_decCall _ _ _ _ _ _ _ originalRuntimeCode_scratchAllocation_lookup (by simp)
    scratchAlloc_acallee (fun _ => rfl) ?_ hc (fun _ _ _ _ => trivial)
  · intro F s values callee post v code aw sl _ args lookup run _
    have av : values = [.val (.word 24)] := by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact] at args
      exact args.symm
    subst av
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_scratchAllocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    obtain ⟨hfm,⟨sp,hsp,fmsp,spsp⟩,_⟩ := aw
    obtain ⟨request,within,ew,_⟩ := scratch_alloc_body_returned (callEntryStateHOLFinite s _) post sp 24 FM code hsp
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hfm v run
    obtain ⟨b1,b2⟩ := scratchEnd24_bound sp FM fmsp request within
    exact ⟨_,by simp [HolFiniteMapExact.lookup_update,FUPDATE,ew],b1,by omega⟩


/-- `_rlp_validate_items_body` keeps every word outside the scratch arena `[FM, SP0)` in every outcome (including
`RlpErr` raises and allocator traps), and keeps the arena globals on every continuing outcome. -/
theorem validateBody_aq (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    AQT SP0 P0 FM G0 w (fun x => x ≠ ofString "h") (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact fun _ => rfl
    | exact fun hn => absurd rfl hn
    | exact aqT_assignLocal _ _
    | exact aqT_return _
    | apply aqT_seq
    | apply aqT_while
    | apply aqT_ite
    | apply aqT_dec
    | apply aqT_scratchRec
    | refine aqRec_storeSeq _ _ (rec_addr0 hw) (sl_varV _ (by decide)) ?_
    | refine aqRec_storeSeq _ _ (rec_addr hw _ (by decide)) (sl_varV _ (by decide)) ?_
    | apply aqRec_ofT
    | refine aqT_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpHeader_lookup (by simp)
        (acallee_of_asafe (asafe_mf rlpHeader_memoryFrame)) (fun hn => absurd rfl hn) ?_

theorem validateBody_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM G0 w (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) := by
  have h := validateBody_aq (P0 := P0) (G0 := G0) hw
  unfold AQT at h
  exact acallee_of_aq h


/-- A discarded call whose callee body is arena-safe from entry locals satisfying `Pc`, which the caller's
arguments establish. -/
theorem aq_callP {P Pc : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomOK s.memaddrs →
      AW SP0 P0 FM G0 s.globals →
      SL (fun _ => True) s.locals → Pc s.locals →
      (evaluateHOLFiniteState s body).2.memory w = s.memory w ∧
      (Continuing (evaluateHOLFiniteState s body).1 → AW SP0 P0 FM G0 (evaluateHOLFiniteState s body).2.globals))
    (hpc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals → P s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) → Pc callee) :
    AQ SP0 P0 FM G0 w Vn P P (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl pre
  rw [evaluateHOLFiniteState_call]
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
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
          (hpc state values callee foundShape aw pre args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM G0 bodyPost.globals) at frame
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,pre⟩,by simp,by simp⟩
            | exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- The scratch mark held in local `x` lies in `[FM, SP0]`. -/
def MarkIn (SP0 FM : BitVec 64) (x : MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ m : BitVec 64, L.lookup x = some (.val (.word m)) ∧ FM.toNat ≤ m.toNat ∧ m.toNat ≤ SP0.toNat

theorem source_scratchRelease_body : sourceFunctionBody Guest.guestFn_scratch_release =
    .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- `scratch_release(x)` with a mark in `[FM, SP0]` keeps the watched word and the arena globals. -/
theorem aq_releaseCall {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (x : MlS)
    (hx : ∀ L, P L → MarkIn SP0 FM x L) :
    AQ SP0 P0 FM G0 w Vn P P (.call (some (none,none)) (ofString "scratch_release") [.var .local x]) := by
  refine aq_callP (Pc := MarkIn SP0 FM (ofString "m")) _ _ _ _ _ originalRuntimeCode_scratchRelease_lookup (by simp)
    ?_ ?_
  · intro F s code dom aw sl pc
    rw [source_scratchRelease_body]
    have hs : AQ SP0 P0 FM G0 w (fun _ => True) (MarkIn SP0 FM (ofString "m")) (fun _ => True)
        (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0))) := by
      refine aq_seq (Q := MarkIn SP0 FM (ofString "m")) (aq_assignScratch _ ?_) (aq_return _)
      intro F s v _ ⟨m,hm,lo,hi⟩ _ ev
      simp [EV,evalHOLExact,hm] at ev
      subst ev
      exact ⟨m,rfl,lo,hi⟩
    have h := hs F s code dom aw sl pc
    exact ⟨h.1,h.2.1⟩
  · intro F s values callee rs _ pre args lookup
    obtain ⟨m,hm,lo,hi⟩ := hx _ pre
    have av : values = [.val (.word m)] := by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hm] at args
      exact args.symm
    subst av
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_scratchRelease_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨m,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi⟩

theorem scratchRelease_memKeep : MemKeep (sourceFunctionBody Guest.guestFn_scratch_release) := by
  rw [source_scratchRelease_body]
  exact memKeep_seq (memKeep_assign _ _ _) (memKeep_leaf _ (by decide))

/-- The `rlp_validate_items` handler `scratch_release(x); throw eid e` keeps all memory and never continues. -/
theorem releaseRaise_handler (x eid : MlS) (e : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (.seq (.call (some (none,none)) (ofString "scratch_release") [.var .local x])
        (.raise eid e))).2.memory w = s.memory w ∧
      ¬ Continuing (evaluateHOLFiniteState s (.seq (.call (some (none,none)) (ofString "scratch_release")
        [.var .local x]) (.raise eid e))).1 := by
  have mk := memKeep_seq (memKeep_discardCall (ofString "scratch_release") [.var .local x] _ _ _
    originalRuntimeCode_scratchRelease_lookup scratchRelease_memKeep) (memKeep_leaf (.raise eid e) rfl) s code
  refine ⟨by rw [mk],?_⟩
  have nr := discard_call_not_returned s (ofString "scratch_release") [.var .local x]
  have lc := discard_call_not_loopControl s (ofString "scratch_release") [.var .local x]
  rw [evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "scratch_release") [.var .local x]) with
  | mk r t =>
    rw [hr] at lc
    have nr' : ∀ v, r ≠ some (.returned v) := fun v => by have := nr v; rw [hr] at this; exact this
    cases r with
    | none =>
      dsimp only
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only
        split <;> exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h
      · exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h
    | some y =>
      dsimp only
      rintro (h | h | h | ⟨v,h⟩)
      · cases h
      · exact lc.1 h
      · exact lc.2 h
      · exact nr' v h

/-- `rlp_validate_items` keeps every word outside the scratch arena in every outcome (including `RlpErr` re-raises
after the handler's scratch release), and keeps the arena globals on every continuing outcome. -/
theorem rlpValidate_aq (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    AQ SP0 P0 FM G0 w (fun _ => True) (fun _ => True) (fun _ => True)
      (sourceFunctionBody Guest.guestFn_rlp_validate_items) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  refine aq_decCall (Pc := MarkIn SP0 FM (ofString "mark")) (Qc := fun _ => True) _ _ _ _ _ _ _
    originalRuntimeCode_scratchMark_lookup (by simp)
    (acallee_of_aq (Vn' := fun _ => True) (Q := fun _ => True) (by rw [source_scratchMark_body]; exact aq_return _))
    (fun _ => rfl) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v _ aw _ _ _ _ run _
    obtain ⟨_,⟨sp,hsp,lo,hi⟩,_⟩ := aw
    rw [source_scratchMark_body,evaluateHOLFiniteState_return] at run
    have ev : EV (callEntryStateHOLFinite s callee) (.var .global (ofString "scratch_ptr")) =
        some (.val (.word sp)) := by
      simp [EV,evalHOLExact,callEntryStateHOLFinite,hsp]
    simp only [EV] at ev
    rw [ev] at run
    dsimp only at run
    split at run
    · obtain ⟨e1,_⟩ := Prod.mk.inj run
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e1
      subst e1
      exact ⟨sp,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,hi⟩
    · cases (Prod.mk.inj run).1
  refine aq_dec (Pb := MarkIn SP0 FM (ofString "mark")) (Qb := fun _ => True) _ _ _ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ => trivial)
  · intro F s v _ ⟨m,hm,lo,hi⟩ _ _ _
    exact ⟨m,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hm],lo,hi⟩
  refine aq_seq (aq_callHandler _ _ _ _ _ _ _ _ originalRuntimeCode_rlpValidationBody_lookup (by simp)
    (validateBody_acallee hw) (fun s code => releaseRaise_handler _ _ _ s code))
    (aq_seq (aq_releaseCall _ (fun _ h => h)) (aq_return _))

theorem rlpValidate_acallee (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) :
    ACallee SP0 P0 FM G0 w (sourceFunctionBody Guest.guestFn_rlp_validate_items) :=
  acallee_of_aq (rlpValidate_aq hw)

#print axioms validateBody_acallee
#print axioms aq_releaseCall
#print axioms releaseRaise_handler
#print axioms rlpValidate_acallee
end InitECandidate.Runtime
