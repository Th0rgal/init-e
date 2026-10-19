import InitECandidate.Runtime.RlpSlicesArena
import InitECandidate.Runtime.VmFn_mpt_fail
import InitECandidate.Runtime.OriginalMemzeroCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- A discarded call whose body never continues never continues. -/
theorem neverCall_noncont (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hn : ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ¬ Continuing (evaluateHOLFiniteState s body).1) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    ¬ Continuing (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 := by
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h
      · have nb := hn F (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at nb
          change ¬ Continuing rb at nb
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | exact absurd (Or.inl rfl) nb
            | exact absurd (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))) nb
            | exact fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h

/-- A discarded call whose body keeps memory and never continues: it keeps memory and never continues. -/
theorem aq_neverCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hm : MemKeep body)
    (hn : ∀ (F : Type) (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ¬ Continuing (evaluateHOLFiniteState s body).1) :
    AQ SP0 P0 FM G0 w Vn P Q (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl pre
  have mk := memKeep_discardCall function arguments _ _ _ installed hm state code
  have nc := neverCall_noncont function arguments parameters body returnShape installed hn state code
  exact ⟨by rw [mk],fun c => absurd c nc,fun e => absurd (Or.inl e) nc,fun e => nc (Or.inr (Or.inl e)),
    fun e => nc (Or.inr (Or.inr (Or.inl e)))⟩

theorem mptFail_memKeep : MemKeep (sourceFunctionBody Guest.guestFn_mpt_fail) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact memKeep_seq (memKeep_leaf _ rfl) (memKeep_leaf _ rfl)

theorem source_mptFail_body : sourceFunctionBody Guest.guestFn_mpt_fail =
    .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem raise_not_continuing {F : Type} (s : PanSemStateFiniteExact 64 F) (eid : MlS) (e : ExpHOL 64) :
    ∃ x, (evaluateHOLFiniteState s (.raise eid e)).1 = some x ∧ ¬ Continuing (some x) := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · exact ⟨_,rfl,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩
    · exact ⟨_,rfl,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩
  · exact ⟨_,rfl,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩

theorem mptFail_never (F : Type) (s : PanSemStateFiniteExact 64 F) (_code : s.code = originalRuntimeCode) :
    ¬ Continuing (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_mpt_fail)).1 := by
  rw [source_mptFail_body,evaluateHOLFiniteState_seq_line780]
  obtain ⟨x,hx,nc⟩ := raise_not_continuing s (ofString "MptErr") (.var .local (ofString "code"))
  cases hr : evaluateHOLFiniteState s (.raise (ofString "MptErr") (.var .local (ofString "code"))) with
  | mk r t =>
    rw [hr] at hx
    subst hx
    exact nc

theorem aq_mptFail {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (arguments : List (ExpHOL 64)) :
    AQ SP0 P0 FM G0 w Vn P Q (.call (some (none,none)) (ofString "mpt_fail") arguments) :=
  aq_neverCall _ _ _ _ _ vmLookup_mpt_fail mptFail_memKeep mptFail_never

/-- A call with a local result destination and an exception handler that never continues. -/
theorem aq_callHandlerDest {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (x : MlS) (hx : ¬ Vn x)
    (hq : ∀ L v, P L → Q (L.update (x,v))) (function : MlS)
    (arguments : List (ExpHOL 64)) (eid ev : MlS) (handler : ProgHOL 64)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM G0 w body)
    (hh : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      (evaluateHOLFiniteState s handler).2.memory w = s.memory w ∧ ¬ Continuing (evaluateHOLFiniteState s handler).1) :
    AQ SP0 P0 FM G0 w Vn P Q (.call (some (some (.local,x),some (eid,ev,handler))) function arguments) := by
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
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        (by rw [← code]; exact lookup)
      split
      · exact aq_of_not_continuing rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb F (callEntryStateHOLFinite state callee) code dom aw esl
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM G0 bodyPost.globals) at frame
          obtain ⟨H,hH⟩ : ∃ H : PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F,
              H = fun t => evaluateHOLFiniteState t handler := ⟨_,rfl⟩
          have hh' : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
              (H t).2.memory w = t.memory w ∧ ¬ Continuing (H t).1 := by subst hH; exact fun t c => hh t c
          have eqH : ∀ t : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState t handler = H t := by
            subst hH; intro; rfl
          simp only [eqH]
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (repeat' split)
          all_goals first
            | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl x _ (fun h => absurd h hx),hq _ _ pre⟩,by simp,by simp⟩
            | exact aq_of_not_continuing frame.1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | (refine aq_of_not_continuing ((hh' _ ?_).1.trans frame.1) (hh' _ ?_).2 <;>
                exact meta'.1.trans code)

/-- The account record `acct_out = A` fits below `2^64` and the watched word is outside `[A, A + 56)`. -/
def AcctOut (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ A : BitVec 64, L.lookup (ofString "acct_out") = some (.val (.word A)) ∧ A.toNat + 56 < 2^64 ∧
    (w.toNat < A.toNat ∨ A.toNat + 56 ≤ w.toNat)

theorem acct_off_ne {A : BitVec 64} (hA : A.toNat + 56 < 2^64) (hw : w.toNat < A.toNat ∨ A.toNat + 56 ≤ w.toNat)
    (k : BitVec 64) (hk : k.toNat < 56) : w ≠ A + k := by
  intro e
  have : (A + k).toNat = A.toNat + k.toNat := by rw [BitVec.toNat_add_of_lt (by omega)]
  rw [← e] at this
  omega

theorem acct_memzero_out {A : BitVec 64} (hA : A.toNat + 56 < 2^64)
    (hw : w.toNat < A.toNat ∨ A.toNat + 56 ≤ w.toNat) : ¬ MWin (A + 8) (32 : BitVec 64).toNat w := by
  rintro ⟨j,hj,h | h⟩
  · have hj' : j < 32 := hj
    have : (A + 8 + BitVec.ofNat 64 j).toNat = A.toNat + 8 + j := by
      rw [BitVec.toNat_add_of_lt,BitVec.toNat_add_of_lt] <;> simp <;> omega
    rw [← h] at this
    omega
  · have hj' : j < 32 := hj
    have e1 : (A + 8 + BitVec.ofNat 64 j).toNat = A.toNat + 8 + j := by
      rw [BitVec.toNat_add_of_lt,BitVec.toNat_add_of_lt] <;> simp <;> omega
    have e2 := panByteAlign_toNat64 (A + 8 + BitVec.ofNat 64 j)
    rw [e1,← h] at e2
    have := Nat.div_mul_le_self (A.toNat + 8 + j) 8
    have := Nat.lt_div_mul_add (a := A.toNat + 8 + j) (b := 8) (by omega)
    omega

/-- `memzero(acct_out + 8, 32)` keeps the watched word outside the account record and the arena globals. -/
theorem aq_memzeroAcct {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (hP : ∀ L, P L → AcctOut w L) :
    AQ SP0 P0 FM G0 w Vn P P (.call (some (none,none)) (ofString "memzero")
      [.op .add [.var .local (ofString "acct_out"),.const 8],.const 32]) := by
  refine aq_callP (Pc := fun L => ∃ D : BitVec 64, L.lookup (ofString "dst") = some (.val (.word D)) ∧
      L.lookup (ofString "n") = some (.val (.word 32)) ∧ ¬ MWin D (32 : BitVec 64).toNat w)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp) ?_ ?_
  · intro F s code _ aw _ ⟨D,hd,hn,out⟩
    refine ⟨memzero_body_window s D 32 w hd hn (by decide) out,fun _ => ?_⟩
    rw [memzero_body_globals_frame s code]
    exact aw
  · intro F s values callee rs _ pre args lookup
    obtain ⟨A,hA,fit,hw⟩ := hP _ pre
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,wordOpHOL,wordOp,valueIsWord,valueWord] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_memzero_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨A + 8,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],acct_memzero_out fit hw⟩

/-- Agreement with a reference map on the names `S`. -/
def Fix (L0 : HolFiniteMapExact MlS (ValueHOL 64)) (S : List MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ z ∈ S, L.lookup z = L0.lookup z

/-- Facts `Fa` about a reference map that the current locals agree with on `S`. -/
def FP (Fa : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (S : List MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    Prop :=
  ∃ L0, Fa L0 ∧ Fix L0 S L

/-- Stability of a locals predicate under writes and scope restores of one name. -/
def Stab (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (x : MlS) : Prop :=
  (∀ L v, P L → P (L.update (x,v))) ∧ (∀ L o, P L → P (L.resVarEq (x,o)))

theorem stab_FP (Fa : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (S : List MlS) (x : MlS) (hx : x ∉ S) :
    Stab (FP Fa S) x := by
  constructor
  · rintro L v ⟨L0,fa,fx⟩
    refine ⟨L0,fa,fun z hz => ?_⟩
    have ne : z ≠ x := fun e => hx (e ▸ hz)
    rw [← fx z hz]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  · rintro L o ⟨L0,fa,fx⟩
    refine ⟨L0,fa,fun z hz => ?_⟩
    have ne : z ≠ x := fun e => hx (e ▸ hz)
    rw [← fx z hz]; exact resVar_lookup_ne L x z o ne

theorem fp_self (Fa : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (S : List MlS) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (h : Fa L) : FP Fa S L := ⟨L,h,fun _ _ => rfl⟩

theorem aqS_dec {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hs : Stab P name) (hshape : Vn name → shape = .one) (hb : AQ SP0 P0 FM G0 w Vn P P body) :
    AQ SP0 P0 FM G0 w Vn P P (.dec name shape init body) :=
  aq_dec name shape init hshape (fun _ _ _ pre _ _ _ => hs.1 _ _ pre) hb (fun _ _ _ h => hs.2 _ _ h)

theorem aqS_assign {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (x : MlS) (e : ExpHOL 64) (hs : Stab P x) :
    AQ SP0 P0 FM G0 w Vn P P (.assign .local x e) :=
  aq_assignLocal x e (fun _ _ _ pre _ _ => hs.1 _ _ pre)

theorem aqS_while {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQ SP0 P0 FM G0 w Vn P P body) : AQ SP0 P0 FM G0 w Vn P P (.while c body) :=
  aq_while (C := fun _ => True) c (fun _ _ _ _ _ _ _ => trivial) (aq_conseq hb (fun _ h => h.1) (fun _ h => h))

theorem aqS_ite {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (c : ExpHOL 64) {y n : ProgHOL 64}
    (hy : AQ SP0 P0 FM G0 w Vn P P y) (hn : AQ SP0 P0 FM G0 w Vn P P n) : AQ SP0 P0 FM G0 w Vn P P (.ite c y n) :=
  aq_ite (CT := fun _ => True) (CF := fun _ => True) c (fun _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aq_conseq hy (fun _ h => h.1) (fun _ h => h)) (aq_conseq hn (fun _ h => h.1) (fun _ h => h))

theorem aqS_decCall {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hb : ACallee SP0 P0 FM G0 w body) (hshape : Vn name → shape = .one)
    (hs : Stab P name) (hc : AQ SP0 P0 FM G0 w Vn P P cont) :
    AQ SP0 P0 FM G0 w Vn P P (.decCall name shape function arguments cont) :=
  aq_decCall name function shape arguments parameters body returnShape installed allOne hb hshape
    (fun _ _ _ _ _ _ _ _ pre _ _ _ _ => hs.1 _ _ pre) hc (fun _ _ _ h => hs.2 _ _ h)

/-- The `RlpErr` handler `mpt_fail(k)` keeps all memory and never continues, from any state. -/
theorem mptFailCall_handler (arguments : List (ExpHOL 64)) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") arguments)).2.memory w = s.memory w ∧
      ¬ Continuing (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") arguments)).1 :=
  ⟨by rw [memKeep_discardCall _ arguments _ _ _ vmLookup_mpt_fail mptFail_memKeep s code],
    neverCall_noncont _ arguments _ _ _ vmLookup_mpt_fail mptFail_never s code⟩

/-- A four-word struct local. -/
def S4 (x : MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ a b c d : BitVec 64, L.lookup x = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)])

theorem shape4 {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one,.one,.one]) = true) :
    ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)] := by
  rcases v with ⟨⟨x⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨⟨⟨a⟩⟩ | _ | _,_ | ⟨⟨⟨b⟩⟩ | _ | _,_ | ⟨⟨⟨c⟩⟩ | _ | _,_ | ⟨⟨⟨d⟩⟩ | _ | _,_ | ⟨_,_⟩⟩⟩⟩⟩ <;>
      simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact,shapeEqHOL] at h

theorem acctOut_congr {L L' : HolFiniteMapExact MlS (ValueHOL 64)}
    (e : L.lookup (ofString "acct_out") = L'.lookup (ofString "acct_out")) (h : AcctOut w L') : AcctOut w L := by
  obtain ⟨A,hA,f,o⟩ := h; exact ⟨A,e.trans hA,f,o⟩

theorem s4_congr {x : MlS} {L L' : HolFiniteMapExact MlS (ValueHOL 64)} (e : L.lookup x = L'.lookup x)
    (h : S4 x L') : S4 x L := by
  obtain ⟨a,b,c,d,h⟩ := h; exact ⟨a,b,c,d,e.trans h⟩

/-- A word store at `acct_out + k` (`k < 56`). -/
theorem aq_storeAcct {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (k : BitVec 64) (hk : k.toNat < 56)
    (hP : ∀ L, P L → AcctOut w L) (v : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, AW SP0 P0 FM G0 s.globals → P s.locals →
      SL Vn s.locals → EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQ SP0 P0 FM G0 w Vn P P (.store (.op .add [.var .local (ofString "acct_out"),.const k]) v) := by
  refine aq_store _ _ (fun s _ pre _ => ?_) hv
  obtain ⟨A,hA,fit,hw⟩ := hP _ pre
  exact ⟨A + k,by simp [EV,evalHOLExact,evalListHOLExact,hA,wordOpHOL,wordOp,valueIsWord,valueWord],
    acct_off_ne fit hw k hk⟩

/-- A static global holds a one-word value. -/
theorem static_word {F : Type} (s : PanSemStateFiniteExact 64 F) (aw : AW SP0 P0 FM G0 s.globals) (n : MlS)
    (hn : n ∈ staticGlobalNames) (x : ValueHOL 64) (ev : EV s (.var .global n) = some x) :
    ∃ y : BitVec 64, x = .val (.word y) := by
  obtain ⟨e1,y,e2⟩ := aw.2.2.2 n hn
  simp [EV,evalHOLExact] at ev
  rw [e1,e2] at ev
  exact ⟨y,(Option.some.inj ev).symm⟩

theorem s4_field {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (h : S4 x s.locals) (i : Nat)
    (v : ValueHOL 64) (ev : EV s (.rfield i (.var .local x)) = some v) : ∃ y : BitVec 64, v = .val (.word y) := by
  obtain ⟨a,b,c,d,h⟩ := h
  simp [EV,evalHOLExact,h] at ev
  rcases i with _ | _ | _ | _ | i <;> simp at ev <;> first | exact ⟨_,ev.symm⟩ | simp at ev

/-- The four struct locals of the account decoder. -/
def acctNames : List MlS := [ofString "acct_out",ofString "f1",ofString "f2",ofString "f3"]

/-- Decoder facts: the account window and the three four-word field items. -/
def Fa4 (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  AcctOut w L ∧ S4 (ofString "f1") L ∧ S4 (ofString "f2") L ∧ S4 (ofString "f3") L

/-- The balance item has at most 32 bytes. -/
def F1b (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ a b c d : BitVec 64, L.lookup (ofString "f1") =
    some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]) ∧ c.toNat ≤ 32

def FaB (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop := Fa4 w L ∧ F1b L

theorem faB_of_fp {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : FP (FaB w) acctNames L) : FaB w L := by
  obtain ⟨L0,⟨⟨ao,s1,s2,s3⟩,f1b⟩,fx⟩ := h
  have e0 := fx (ofString "acct_out") (by simp [acctNames])
  have e1 := fx (ofString "f1") (by simp [acctNames])
  have e2 := fx (ofString "f2") (by simp [acctNames])
  have e3 := fx (ofString "f3") (by simp [acctNames])
  obtain ⟨a,b,c,d,hf,hc⟩ := f1b
  exact ⟨⟨acctOut_congr e0 ao,s4_congr e1 s1,s4_congr e2 s2,s4_congr e3 s3⟩,⟨a,b,c,d,e1.trans hf,hc⟩⟩

/-- Balance loop guard: `i < f1.2`. -/
def BalC (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ i a b c d : BitVec 64, L.lookup (ofString "i") = some (.val (.word i)) ∧
    L.lookup (ofString "f1") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]) ∧
    i.toNat < c.toNat

/-- `pos = f1.2 - 1 - i` is at most 31. -/
def BalPos (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  FP (FaB w) acctNames L ∧ ∃ p : BitVec 64, L.lookup (ofString "pos") = some (.val (.word p)) ∧ p.toNat ≤ 31

/-- `lp` lies in `[A + 8, A + 32]`. -/
def BalLp (w : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  FP (FaB w) acctNames L ∧ ∃ A l : BitVec 64, A.toNat + 56 < 2^64 ∧ (w.toNat < A.toNat ∨ A.toNat + 56 ≤ w.toNat) ∧
    L.lookup (ofString "lp") = some (.val (.word l)) ∧ A.toNat + 8 ≤ l.toNat ∧ l.toNat ≤ A.toNat + 32

theorem aq_balance (ve : List (ExpHOL 64)) (ie : ExpHOL 64) :
    AQ SP0 P0 FM G0 w Vn (FP (FaB w) acctNames) (FP (FaB w) acctNames)
      (.while (.cmp .lower (.var .local (ofString "i")) (.rfield 2 (.var .local (ofString "f1"))))
        (.dec (ofString "pos") .one
          (.op .sub [.op .sub [.rfield 2 (.var .local (ofString "f1")),.const 1],.var .local (ofString "i")])
          (.dec (ofString "lp") .one (.op .add [.var .local (ofString "acct_out"),.const 8,
              .panop .mul [.shift .lsr (.var .local (ofString "pos")) (.const 3),.const 8]])
            (.seq (.store (.var .local (ofString "lp")) (.op .or ve)) (.assign .local (ofString "i") ie))))) := by
  have sI : ∀ x, x ∉ acctNames → Stab (FP (FaB w) acctNames) x := fun x hx => stab_FP _ _ x hx
  refine aq_while (C := BalC) _ ?_ ?_
  · intro F s x _ pre _ ev nz
    obtain ⟨_,a,b,c,d,hf,_⟩ := faB_of_fp pre
    cases hi : s.locals.lookup (ofString "i") with
    | none => simp [EV,evalHOLExact,hi] at ev
    | some iv =>
      rcases iv with ⟨⟨i⟩⟩ | fs | ⟨n,fs⟩
      · refine ⟨i,a,b,c,d,hi,hf,?_⟩
        simp [EV,evalHOLExact,hi,hf] at ev
        by_contra hge
        have cf : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower i c = false := by
          change decide (i.toNat < c.toNat) = false
          exact decide_eq_false hge
        rw [cf] at ev
        exact nz (by simpa using ev.symm)
      all_goals simp [EV,evalHOLExact,hi] at ev
  refine aq_dec (Pb := BalPos w) (Qb := FP (FaB w) acctNames) _ _ _ (fun _ => rfl) ?_ ?_
    (fun _ _ _ h => (sI _ (by decide)).2 _ _ h)
  · intro F s v _ ⟨pre,i,a,b,c,d,hi,hf,lt⟩ _ ev _
    obtain ⟨_,⟨a',b',c',d',hf',hc⟩⟩ := faB_of_fp pre
    rw [hf] at hf'
    simp only [Option.some.injEq,ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,
      and_true] at hf'
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hf'
    simp [EV,evalHOLExact,evalListHOLExact,hi,hf,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨(sI _ (by decide)).1 _ _ pre,c - 1#64 - i,by simp [HolFiniteMapExact.lookup_update,FUPDATE],?_⟩
    have h1 : (c - 1#64).toNat = c.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega))]; simp
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)),h1]
    omega
  refine aq_dec (Pb := BalLp w) (Qb := FP (FaB w) acctNames) _ _ _ (fun _ => rfl) ?_ ?_
    (fun _ _ _ h => (sI _ (by decide)).2 _ _ h)
  · intro F s v _ ⟨pre,p,hp,hp31⟩ _ ev _
    obtain ⟨⟨⟨A,hA,fit,hw⟩,_⟩,_⟩ := faB_of_fp pre
    simp [EV,evalHOLExact,evalListHOLExact,hA,hp,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,wordShiftHOL] at ev
    subst ev
    have e1 : (p >>> 3).toNat = p.toNat / 8 := by
      simp [Nat.shiftRight_eq_div_pow]
    have e2 : (p >>> 3 * 8#64).toNat = p.toNat / 8 * 8 := by
      rw [BitVec.toNat_mul,e1]; simp; omega
    have e3 : (8#64 + p >>> 3 * 8#64).toNat = 8 + p.toNat / 8 * 8 := by
      rw [BitVec.toNat_add,e2]; simp; omega
    have e4 : (A + (8#64 + p >>> 3 * 8#64)).toNat = A.toNat + 8 + p.toNat / 8 * 8 := by
      rw [BitVec.toNat_add,e3]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    refine ⟨(sI _ (by decide)).1 _ _ pre,A,A + (8#64 + p >>> 3 * 8#64),fit,hw,
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],by omega,by omega⟩
  refine aq_seq (aq_store (P := BalLp w) _ _ ?_ ?_) (aq_assignLocal _ _ ?_)
  · intro F s _ ⟨_,A,l,fit,hw,hl,lo,hi⟩ _
    refine ⟨l,by simp [EV,evalHOLExact,hl],fun e => ?_⟩
    subst e
    omega
  · intro F s x _ _ _ ev
    exact ev_op_word s _ _ x ev
  · intro F s v _ ⟨pre,_⟩ _ _
    exact (sI _ (by decide)).1 _ _ pre

/-- Scalar names of the account decoder: everything except its struct locals. -/
def VnA (x : MlS) : Prop :=
  x ≠ ofString "it" ∧ x ≠ ofString "sl" ∧ x ≠ ofString "f0" ∧ x ≠ ofString "f1" ∧ x ≠ ofString "f2" ∧
    x ≠ ofString "f3"

theorem fp_weaken {Fa Fb : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {S S' : List MlS}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : FP Fa S L) (hf : ∀ L0, Fa L0 → Fb L0) (hs : ∀ z ∈ S', z ∈ S) :
    FP Fb S' L := by
  obtain ⟨L0,fa,fx⟩ := h
  exact ⟨L0,hf _ fa,fun z hz => fx z (hs z hz)⟩

/-- `x = rlp_item(..)` (a four-word struct): the continuation additionally knows that `x` holds four words. -/
theorem aq_decCallItem {Fa : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {S : List MlS} (x : MlS) (hx : x ∉ S)
    (fa_congr : ∀ L L', Fix L' S L → Fa L' → Fa L) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hvx : ¬ Vn x)
    (hc : AQ SP0 P0 FM G0 w Vn (FP (fun L => Fa L ∧ S4 x L) (S ++ [x])) (FP (fun L => Fa L ∧ S4 x L) (S ++ [x]))
      cont) :
    AQ SP0 P0 FM G0 w Vn (FP Fa S) (FP Fa S)
      (.decCall x (.comb [.one,.one,.one,.one]) (ofString "rlp_item") arguments cont) := by
  refine aq_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpItem_lookup (by simp) (rlpItem_acallee hw)
    (fun h => absurd h hvx) ?_ hc ?_
  · intro F s values callee post v _ _ _ ⟨L0,fa,fx⟩ _ _ _ ok
    refine fp_self _ _ _ ⟨fa_congr _ _ (fun z hz => ?_) fa,?_⟩
    · have ne : z ≠ x := fun e => hx (e ▸ hz)
      rw [← fx z hz]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    · obtain ⟨a,b,c,d,rfl⟩ := shape4 ok
      exact ⟨a,b,c,d,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩
  · intro L L' _ h
    exact (stab_FP Fa S x hx).2 _ _ (fp_weaken h (fun _ h => h.1) (fun z hz => List.mem_append_left _ hz))

theorem fp4_to_B {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : FP (Fa4 w) acctNames L) (hb : F1b L) :
    FP (FaB w) acctNames L := by
  obtain ⟨L0,⟨ao,s1,s2,s3⟩,fx⟩ := h
  have e0 := fx (ofString "acct_out") (by simp [acctNames])
  have e1 := fx (ofString "f1") (by simp [acctNames])
  have e2 := fx (ofString "f2") (by simp [acctNames])
  have e3 := fx (ofString "f3") (by simp [acctNames])
  exact fp_self _ _ _ ⟨⟨acctOut_congr e0 ao,s4_congr e1 s1,s4_congr e2 s2,s4_congr e3 s3⟩,hb⟩

theorem fa4_of_fp {L : HolFiniteMapExact MlS (ValueHOL 64)} (h : FP (Fa4 w) acctNames L) : Fa4 w L := by
  obtain ⟨L0,⟨ao,s1,s2,s3⟩,fx⟩ := h
  exact ⟨acctOut_congr (fx (ofString "acct_out") (by simp [acctNames])) ao,
    s4_congr (fx (ofString "f1") (by simp [acctNames])) s1,s4_congr (fx (ofString "f2") (by simp [acctNames])) s2,
    s4_congr (fx (ofString "f3") (by simp [acctNames])) s3⟩

set_option maxHeartbeats 4000000 in
/-- `decode_account_from_leaf` keeps every word outside the account record `[acct_out, acct_out + 56)`, below `P0`
and outside the scratch arena, in every outcome (`RlpErr` re-raised as `MptErr`, every `mpt_fail` check, allocator
traps), and keeps the arena globals on continuing outcomes. -/
theorem decodeAcct_aq (hw : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hp : w.toNat < P0.toNat) :
    AQ SP0 P0 FM G0 w VnA (AcctOut w) (fun _ => True)
      (sourceFunctionBody Guest.guestFn_decode_account_from_leaf) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_decode_account_from_leaf,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  have sA : ∀ x, x ∉ [ofString "acct_out"] → Stab (FP (AcctOut w) [ofString "acct_out"]) x :=
    fun x hx => stab_FP _ _ x hx
  have s4 : ∀ x, x ∉ acctNames → Stab (FP (Fa4 w) acctNames) x := fun x hx => stab_FP _ _ x hx
  have sB : ∀ x, x ∉ acctNames → Stab (FP (FaB w) acctNames) x := fun x hx => stab_FP _ _ x hx
  refine aq_conseq (P := FP (AcctOut w) [ofString "acct_out"]) (Q := FP (AcctOut w) [ofString "acct_out"]) ?_
    (fun L h => fp_self _ _ L h) (fun _ _ => trivial)
  refine aqS_dec _ _ _ (sA _ (by decide)) (fun h => absurd rfl h.1) ?_
  refine aqS_dec _ _ _ (sA _ (by decide)) (fun _ => rfl) ?_
  refine aq_seq (aq_callHandlerDest (ofString "it") (fun h => h.1 rfl) (fun L v h => (sA _ (by decide)).1 L v h)
    _ _ _ _ _ _ _ _ originalRuntimeCode_rlpDecodeFully_lookup (by simp) (rlpDecodeFully_acallee hw)
    (fun s code => mptFailCall_handler _ s code)) ?_
  refine aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) ?_
  refine aqS_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpSlices_lookup (by simp) (rlpSlices_acallee hw hp)
    (fun h => absurd rfl h.2.1) (sA _ (by decide)) ?_
  refine aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) ?_
  refine aqS_dec _ _ _ (sA _ (by decide)) (fun _ => rfl) ?_
  refine aqS_decCall _ _ _ _ _ _ _ originalRuntimeCode_rlpItem_lookup (by simp) (rlpItem_acallee hw)
    (fun h => absurd rfl h.2.2.1) (sA _ (by decide)) ?_
  refine aq_decCallItem _ (by decide) (fun L L' fx h => acctOut_congr (fx _ (by simp)) h) _ hw
    (fun h => h.2.2.2.1 rfl) ?_
  refine aq_decCallItem _ (by decide)
    (fun L L' fx h => ⟨acctOut_congr (fx _ (by simp)) h.1,s4_congr (fx _ (by simp)) h.2⟩) _ hw
    (fun h => h.2.2.2.2.1 rfl) ?_
  refine aq_decCallItem _ (by decide)
    (fun L L' fx h => ⟨⟨acctOut_congr (fx _ (by simp)) h.1.1,s4_congr (fx _ (by simp)) h.1.2⟩,
      s4_congr (fx _ (by simp)) h.2⟩) _ hw (fun h => h.2.2.2.2.2 rfl) ?_
  refine aq_conseq (P := FP (Fa4 w) acctNames) (Q := FP (Fa4 w) acctNames) ?_
    (fun L h => fp_weaken h (fun _ h => ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩) (fun z hz => by
      simp [acctNames] at hz; simp; tauto))
    (fun L h => fp_weaken h (fun _ h => ⟨⟨⟨h.1,h.2.1⟩,h.2.2.1⟩,h.2.2.2⟩) (fun z hz => by
      simp at hz; simp [acctNames]; tauto))
  refine aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) ?_
  refine aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) ?_
  refine aqS_dec _ _ _ (s4 _ (by decide)) (fun _ => rfl) ?_
  refine aqS_dec _ _ _ (s4 _ (by decide)) (fun _ => rfl) ?_
  refine aq_seq (aqS_while _ (aq_seq (aqS_assign _ _ (s4 _ (by decide))) (aqS_assign _ _ (s4 _ (by decide))))) ?_
  refine aq_seq (aq_storeAcct _ (by decide) (fun L h => (fa4_of_fp h).1) _
    (fun s x _ _ sl ev => sl_varV (G0 := G0) (SP0 := SP0) (P0 := P0) (FM := FM) (R := fun _ => True) _ (by unfold VnA; decide) s x
      (by assumption) trivial sl ev)) ?_
  refine aq_seq (Q := FP (FaB w) acctNames) (aq_ite (CT := fun _ => True) (CF := F1b) _ ?_ (aq_mptFail _)
    (aq_conseq aq_skip (fun L h => h) (fun L h => fp4_to_B h.1 h.2))) ?_
  · intro F s x _ pre _ ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    obtain ⟨_,⟨a,b,c,d,hf⟩,_⟩ := fa4_of_fp pre
    refine ⟨a,b,c,d,hf,?_⟩
    simp [EV,evalHOLExact,hf] at ev
    by_contra hgt
    have ct : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (32#64) c = true := by
      change decide ((32#64).toNat < c.toNat) = true
      exact decide_eq_true (by simp; omega)
    rw [ct] at ev
    simp at ev
  refine aq_seq (aq_memzeroAcct (fun L h => (faB_of_fp h).1.1)) ?_
  refine aq_seq (aqS_assign _ _ (sB _ (by decide))) ?_
  refine aq_seq (aq_balance _ _) ?_
  refine aq_seq (aqS_ite _ (aq_storeAcct _ (by decide) (fun L h => (faB_of_fp h).1.1) _
      (fun s x aw _ _ ev => static_word s aw _ (by decide) x ev))
    (aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) (aq_storeAcct _ (by decide) (fun L h => (faB_of_fp h).1.1) _
      (fun s x _ pre _ ev => s4_field s _ (faB_of_fp pre).1.2.2.1 _ x ev)))) ?_
  refine aq_seq (aqS_ite _ (aq_storeAcct _ (by decide) (fun L h => (faB_of_fp h).1.1) _
      (fun s x aw _ _ ev => static_word s aw _ (by decide) x ev))
    (aq_seq (aqS_ite _ (aq_mptFail _) aq_skip) (aq_storeAcct _ (by decide) (fun L h => (faB_of_fp h).1.1) _
      (fun s x _ pre _ ev => s4_field s _ (faB_of_fp pre).1.2.2.2 _ x ev)))) ?_
  exact aq_return _

#print axioms aq_neverCall
#print axioms aq_callHandlerDest
#print axioms aq_memzeroAcct
#print axioms aq_balance
#print axioms decodeAcct_aq
end InitECandidate.Runtime
