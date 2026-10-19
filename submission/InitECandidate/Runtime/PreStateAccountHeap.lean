import InitECandidate.Runtime.PreStateHeap
import InitECandidate.Runtime.OriginalAcctCode
import InitECandidate.Runtime.FourWordStoreMemoryFrame
import InitECandidate.Runtime.PanThreeWordLookup
/-!
Heap-aware `get_pre_state_account(addr)` (the wrapper called from `prepare_dispatch` and the authorization loop):
`get_pre_state_account_optional` via `preState_aqmh`, then, for an absent account, `acct_empty` -> `acct_new`, which
allocates and writes a fresh 56-byte account above the entry heap pointer.  Includes a four-word struct store rule,
call rules for callees with struct parameters and for calls assigning their result, and the actual lookups.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

theorem source_acctNew_body : sourceFunctionBody Guest.guestFn_acct_new =
    .decCall (ofString "a") .one (ofString "alloc") [(.const 56)]
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 0)]) (.var .local (ofString "nonce")))
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 8)]) (.var .local (ofString "balance")))
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 40)]) (.var .global (ofString "empty_trie_root")))
      (.seq (.store (.op .add [(.var .local (ofString "a")),(.const 48)]) (.var .local (ofString "code_hash")))
      (.return (.var .local (ofString "a"))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_acctEmpty_body : sourceFunctionBody Guest.guestFn_acct_empty =
    .decCall (ofString "a") .one (ofString "acct_new")
      [(.const 0),(.rstruct [(.const 0),(.const 0),(.const 0),(.const 0)]),(.var .global (ofString "empty_code_hash"))]
      (.return (.var .local (ofString "a"))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_preStateAccountW_body : sourceFunctionBody Guest.guestFn_get_pre_state_account =
    .decCall (ofString "a") .one (ofString "get_pre_state_account_optional") [(.var .local (ofString "addr"))]
      (.seq (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1))
        (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_empty") []) .skip)
      (.return (.var .local (ofString "a")))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem store_ctl {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) :
    ((evaluateHOLFiniteState s (.store d v)).1 = none ∨ (evaluateHOLFiniteState s (.store d v)).1 = some .error) ∧
    (evaluateHOLFiniteState s (.store d v)).2.locals = s.locals ∧
    (evaluateHOLFiniteState s (.store d v)).2.globals = s.globals := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- A four-word struct store whose four target words avoid the watched word keeps it; locals and globals are kept. -/
theorem aq_store4 {P : HolFiniteMapExact MlS (ValueHOL 64) → Prop} (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), AW SP0 P0 FM G0 s.globals → P s.locals → SL Vn s.locals →
      ∃ a b0 b1 b2 b3 : BitVec 64, EV s d = some (.val (.word a)) ∧
        EV s v = some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]) ∧
        w ≠ a ∧ w ≠ a + 8#64 ∧ w ≠ a + 16#64 ∧ w ≠ a + 24#64) :
    AQ SP0 P0 FM G0 w Vn P P (.store d v) := by
  intro F s code dom aw sl pre
  obtain ⟨a,b0,b1,b2,b3,ha,hv,n0,n8,n16,n24⟩ := hd s aw pre sl
  have mem := evaluate_fourWordStore_memory_frame s d v a b0 b1 b2 b3 w ha hv n0 n8 n16 n24
  obtain ⟨res,loc,glob⟩ := store_ctl s d v
  refine ⟨mem,fun _ => by rw [glob]; exact aw,fun _ => by rw [loc]; exact ⟨sl,pre⟩,?_,?_⟩ <;>
    rcases res with h | h <;> rw [h] <;> simp

#print axioms aq_store4

/-- Entry facts of `acct_new`: a word nonce, a four-word balance and a word code hash. -/
def AcctNewPre (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  (∃ n : BitVec 64, L.lookup (ofString "nonce") = some (.val (.word n))) ∧
  (∃ b0 b1 b2 b3 : BitVec 64, L.lookup (ofString "balance") =
    some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])) ∧
  (∃ c : BitVec 64, L.lookup (ofString "code_hash") = some (.val (.word c)))

theorem ne_off {A k : BitVec 64} (hw : w.toNat < A.toNat) (hk : A.toNat + k.toNat < 2 ^ 64) : w ≠ A + k := by
  intro e; subst e; rw [BitVec.toNat_add_of_lt hk] at hw; omega

set_option maxHeartbeats 4000000 in
/-- `acct_new` keeps every word below the arena bound: it only allocates a fresh 56-byte account and writes it. -/
theorem acctNew_aq (hw : w.toNat < P0.toNat) :
    AQ SP0 P0 FM G0 w (fun _ => False) AcctNewPre (fun _ => True) (sourceFunctionBody Guest.guestFn_acct_new) := by
  rw [source_acctNew_body]
  refine aq_decCall (Pc := fun L => AcctNewPre L ∧ ∃ A : BitVec 64, L.lookup (ofString "a") = some (.val (.word A)) ∧
      P0.toNat ≤ A.toNat ∧ A.toNat + 56 ≤ 33806089496) (Qc := fun _ => True) _ _ _ _ _ _ _
    originalRuntimeCode_allocation_lookup (by simp) alloc_acallee (fun h => h.elim) ?_ ?_ (fun _ _ _ _ => trivial)
  · intro F s values callee post v code aw _ pre args lookup run _
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    obtain ⟨_,_,⟨hp,hhp,lo,hi,_⟩,_⟩ := aw
    obtain ⟨req,_,ew,_⟩ := alloc_body_returned (callEntryStateHOLFinite s _) post hp 56 code hhp
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) v run
    subst ew
    obtain ⟨⟨n,hn⟩,⟨b0,b1,b2,b3,hb⟩,⟨c,hc⟩⟩ := pre
    refine ⟨⟨⟨n,?_⟩,⟨b0,b1,b2,b3,?_⟩,⟨c,?_⟩⟩,hp,by simp [HolFiniteMapExact.lookup_update,FUPDATE],lo,
      allocationGuard_sum_bound hp 56 hi req⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  have off : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (A k : BitVec 64),
      s.locals.lookup (ofString "a") = some (.val (.word A)) →
      EV s (.op .add [.var .local (ofString "a"),.const k]) = some (.val (.word (A + k))) := by
    intro F s A k hA
    simp [EV,evalHOLExact,evalListHOLExact,hA,wordOpHOL,wordOp,valueIsWord,valueWord]
  refine aq_seq (aq_store _ _ ?_ ?_) (aq_seq (aq_store4 _ _ ?_) (aq_seq (aq_store _ _ ?_ ?_)
    (aq_seq (aq_store _ _ ?_ ?_) (aq_return _))))
  · intro F s _ ⟨_,A,hA,lo,hi⟩ _
    exact ⟨A + 0#64,off s A _ hA,ne_off (by omega) (by simp; omega)⟩
  · intro F s x _ ⟨⟨⟨n,hn⟩,_⟩,_⟩ _ ev
    simp [EV,evalHOLExact,hn] at ev; exact ⟨n,ev.symm⟩
  · intro F s _ ⟨⟨_,⟨b0,b1,b2,b3,hb⟩,_⟩,A,hA,lo,hi⟩ _
    have e8 : (A + 8#64).toNat = A.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
    refine ⟨A + 8#64,b0,b1,b2,b3,off s A _ hA,by simp [EV,evalHOLExact,hb],ne_off (by omega) (by simp; omega),
      ne_off (by rw [e8]; omega) (by rw [e8]; simp; omega),ne_off (by rw [e8]; omega) (by rw [e8]; simp; omega),
      ne_off (by rw [e8]; omega) (by rw [e8]; simp; omega)⟩
  · intro F s _ ⟨_,A,hA,lo,hi⟩ _
    exact ⟨A + 40#64,off s A _ hA,ne_off (by omega) (by simp; omega)⟩
  · intro F s x aw _ _ ev
    obtain ⟨eg,y,hy⟩ := aw.2.2.2 (ofString "empty_trie_root") (by decide)
    simp [EV,evalHOLExact,eg,hy] at ev; exact ⟨y,ev.symm⟩
  · intro F s _ ⟨_,A,hA,lo,hi⟩ _
    exact ⟨A + 48#64,off s A _ hA,ne_off (by omega) (by simp; omega)⟩
  · intro F s x _ ⟨⟨_,_,⟨c,hc⟩⟩,_⟩ _ ev
    simp [EV,evalHOLExact,hc] at ev; exact ⟨c,ev.symm⟩

#print axioms acctNew_aq

/-- `acct_new`'s actual lookup binds its three arguments (word, four-word struct, word). -/
theorem acctNew_lookup (n b0 b1 b2 b3 c : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new")
      [.val (.word n),.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)],.val (.word c)] =
      some (sourceFunctionBody Guest.guestFn_acct_new,
        ((HolFiniteMapExact.empty.update (ofString "nonce",.val (.word n))).update
          (ofString "balance",.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])).update
          (ofString "code_hash",.val (.word c)),.one) := by
  have d12 : ofString "nonce" ≠ ofString "balance" := by decide
  have d13 : ofString "nonce" ≠ ofString "code_hash" := by decide
  have d23 : ofString "balance" ≠ ofString "code_hash" := by decide
  have raw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "acct_new")
      [.val (.word n),.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)],.val (.word c)] =
      some (sourceFunctionBody Guest.guestFn_acct_new,(fun key => if key = ofString "code_hash" then
        some (.val (.word c)) else if key = ofString "balance" then
        some (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]) else
        if key = ofString "nonce" then some (.val (.word n)) else none),.one) := by
    simp [lookupCodeHOLExact,originalRuntimeCode_acctNew_lookup,shapeOfHOLExact,shapeEqHOL,
      shapeEqHOL.shapeEqListHOL,d12,d13,d23]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl,rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (sourceFunctionBody Guest.guestFn_acct_new,locals,ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases three : key = ofString "code_hash"
    · subst key
      simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
    · by_cases two : key = ofString "balance"
      · subst key
        simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,d23,Ne.symm d23]
      · by_cases one : key = ofString "nonce"
        · subst key
          simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,d12,Ne.symm d12,d13,
            Ne.symm d13]
        · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,one,two,three,Ne.symm one,
            Ne.symm two,Ne.symm three]

#print axioms acctNew_lookup

/-- A declared call against a callee spec assuming nothing about the callee's locals (any parameter shapes). -/
theorem aqmh_decCallSpecF {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} 
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → ValueHOL 64 → Mem → BitVec 64 → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQMH SP0 P0 FM G0 w (fun _ => False) (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      ∀ H, HeapIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQMH SP0 P0 FM G0 w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      split
      · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (fun _ h => h.elim) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                obtain ⟨H',hH',rr⟩ := r1 v rfl
                have pc := hret _ _ _ _ _ _ pre rr ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by intro a ha; exact dom a (meta'.2.1 ▸ ha))
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx H' (by exact hH') pc
                refine ⟨m2.trans m1,a2,fun e => ?_,r2,c2,b2⟩
                obtain ⟨sl2,H2,hH2,q2⟩ := n2 e
                exact ⟨sl_restore sl2 sl name,H2,hH2,hq _ _ _ _ _ _ pre q2⟩
              · exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A call assigning its word result to a local, against a callee spec assuming nothing about the callee's
locals. -/
theorem aqmh_callAssignF {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → ValueHOL 64 → Mem → BitVec 64 → Prop)
    (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQMH SP0 P0 FM G0 w (fun _ => False) (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, AW SP0 P0 FM G0 s.globals →
      ∀ H, HeapIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → (∃ y : BitVec 64, v = .val (.word y)) ∧
      Q (L.update (name,v)) M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR (.call (some (some (.local,name),none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      split
      · exact aqmh_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (fun _ h => h.elim) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               obtain ⟨⟨y,hy⟩,q⟩ := hret _ _ _ _ _ _ pre rr
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl _ _ (fun _ => ⟨y,hy⟩),H',hH',q⟩,(fun v e => by cases e),by simp,by simp⟩)
            | exact aqmh_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqmh_decCallSpecF
#print axioms aqmh_callAssignF

/-- `aqm_frame_of_aq` with a locals precondition. -/
theorem aqm_frame_of_aqP {Cond : BitVec 64 → Prop} {P Q' : HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    {p : ProgHOL 64} (h : ∀ x, Cond x → AQ SP0 P0 FM G0 x Vn P Q' p) (hw : Cond w) (M0 : Mem) :
    AQM SP0 P0 FM G0 w Vn (fun L M => P L ∧ M = M0) (fun _ M' => ∀ x, Cond x → M' x = M0 x)
      (fun _ M' => ∀ x, Cond x → M' x = M0 x) p := by
  intro F s code dom aw sl ⟨pre,hm⟩
  subst hm
  obtain ⟨m,a,n,c,b⟩ := h w hw F s code dom aw sl pre
  exact ⟨m,a,fun e => ⟨(n e).1,fun x hx => (h x hx F s code dom aw sl pre).1⟩,
    fun _ _ x hx => (h x hx F s code dom aw sl pre).1,c,b⟩

/-- Heap-aware `acct_new` from heap pointer `H0`: every word below `H0` is kept and the exit heap is at least `H0`. -/
theorem acctNew_aqmh (M0 : Mem) (H0 : BitVec 64) (hw0 : w.toNat < H0.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => False) (fun L M H => AcctNewPre L ∧ M = M0 ∧ H = H0) (fun _ _ _ => True)
      (fun _ M' H' => H0.toNat ≤ H'.toNat ∧ ∀ x : BitVec 64, x.toNat < H0.toNat → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_acct_new) :=
  aqmh_conseq (aqmh_of_aqm (P := fun H L M => H = H0 ∧ (AcctNewPre L ∧ M = M0)) (Q := fun H _ _ => H = H0 ∧ True)
    (RR := fun H _ M' => H = H0 ∧ ∀ x : BitVec 64, x.toNat < H0.toNat → M' x = M0 x)
    (fun H _ => aqm_bound_eq (aqm_conseq (aqm_frame_of_aqP (Cond := fun x => x.toNat < H0.toNat)
      (fun x hx => acctNew_aq (P0 := H0) hx) hw0 M0) (fun _ _ h => h) (fun _ _ _ => trivial) (fun _ _ h => h))))
    (fun L M H ⟨h1,h2,h3⟩ => ⟨h3,h1,h2⟩) (fun _ _ _ _ => trivial)
    (fun v M H' ⟨H,_,hle,e,r⟩ => by subst e; exact ⟨hle,r⟩)

/-- Heap-aware `acct_empty` from heap pointer `H0`: returns a word, every word below `H0` is kept and the exit heap
is at least `H0`. -/
theorem acctEmpty_aqmh (M0 : Mem) (H0 : BitVec 64) (hw0 : w.toNat < H0.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => False) (fun _ M H => M = M0 ∧ H = H0) (fun _ _ _ => True)
      (fun v M' H' => (∃ y : BitVec 64, v = .val (.word y)) ∧ H0.toNat ≤ H'.toNat ∧
        ∀ x : BitVec 64, x.toNat < H0.toNat → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_acct_empty) := by
  rw [source_acctEmpty_body]
  refine aqmh_decCallSpecF
    (Pe := fun _ M0' H0' L M H => AcctNewPre L ∧ M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧ ∀ x : BitVec 64, x.toNat < H0'.toNat → M' x = M0' x)
    (Pc := fun L M H => (∃ y : BitVec 64, L.lookup (ofString "a") = some (.val (.word y))) ∧ H0.toNat ≤ H.toNat ∧
      ∀ x : BitVec 64, x.toNat < H0.toNat → M x = M0 x) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_acctNew_lookup
    (fun _ M0' H0' ⟨_,e⟩ => by subst e; exact acctNew_aqmh M0' H0' hw0) ?_ (fun _ => rfl) ?_
    (aqmh_return _ (fun s v H _ ⟨⟨y,hy⟩,hle,fr⟩ _ ev => ⟨⟨y,by simp [EV,evalHOLExact,hy] at ev; exact ev.symm⟩,hle,fr⟩))
    (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s values callee rs aw H _ ⟨hm,hh⟩ _ args lookup
    obtain ⟨_,y,hy⟩ := aw.2.2.2 (ofString "empty_code_hash") (by decide)
    obtain ⟨eg,_⟩ := aw.2.2.2 (ofString "empty_code_hash") (by decide)
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,eg,hy] at args
    subst args
    rw [acctNew_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨⟨0,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨0,0,0,0,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      ⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,rfl,rfl⟩
  · intro L M H v M' H' ⟨hm,hh⟩ ⟨hle,fr⟩ ok
    subst hm hh
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    exact ⟨⟨y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hle,fr⟩

#print axioms acctNew_aqmh
#print axioms acctEmpty_aqmh

/-- The watched word of `PreTabs` lies below its heap pointer. -/
theorem preTabs_out_below {Ts Bs Ta Tb H : BitVec 64} {M : Mem} (h : PreTabs Ts Bs Ta Tb (fun x => x = w) H M) :
    w.toNat < H.toNat := by
  obtain ⟨lA,_,_,_,_,_,o⟩ := h
  by_contra c
  exact (o w rfl).1 (Or.inr (Or.inr (by omega)))

set_option maxHeartbeats 4000000 in
/-- Heap-aware `get_pre_state_account(addr)` from heap pointer `H0` with both read tables (`PreTabs`): the watched
word is kept in every outcome and every return re-establishes `PreTabs` at the exit heap pointer, also when the
absent account is replaced by a freshly allocated empty account. -/
theorem preStateAccountW_aqmh (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs))) (Ta Tb H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        PreTabs Ts Bs Ta Tb (fun x => x = w) H0 M)
      (fun _ _ _ => True) (fun _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M')
      (sourceFunctionBody Guest.guestFn_get_pre_state_account) := by
  rw [source_preStateAccountW_body]
  refine aqmh_decCallSpec (Vn' := fun x => x ≠ ofString "w")
    (Pe := fun _ _ H0' L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0' ∧
      PreTabs Ts Bs Ta Tb (fun x => x = w) H0' M)
    (RRe := fun _ _ _ _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M')
    (Pc := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_preStateAccount_lookup (by simp)
    (fun _ _ H0' ⟨_,e,_⟩ => by
      subst e
      exact preState_aqmh Ts Bs hTs hBs Ta Tb _ p0 K Pd NB hK0 hPd0 hNB0 safe ws hp) ?_ (fun _ => rfl)
    (fun _ _ _ _ _ _ _ r _ => r) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ H _ ⟨⟨A,hA⟩,he,pt⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args he
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_preStateAccount_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,pt⟩
  refine aqmh_seq (Q := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M)
    (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqmh_conseq aqmh_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqmh_return _ (fun _ _ _ _ h _ _ => h))
  refine aqmh_callAssignF (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' v M' H' => (∃ y : BitVec 64, v = .val (.word y)) ∧ H0'.toNat ≤ H'.toNat ∧
      ∀ x : BitVec 64, x.toNat < H0'.toNat → M' x = M0' x)
    _ _ _ _ _ _ originalRuntimeCode_acctEmpty_lookup
    (fun _ M0' H0' ⟨pt,_⟩ => acctEmpty_aqmh M0' H0' (preTabs_out_below pt)) (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) ?_
  intro L M H v M' H' ⟨pt,_⟩ ⟨wv,hle,fr⟩
  exact ⟨wv,preTabs_frame (preTabs_mono pt hle) (fun x hx => fr x (preTabs_below pt x hx))⟩

#print axioms preStateAccountW_aqmh
end InitECandidate.Runtime
