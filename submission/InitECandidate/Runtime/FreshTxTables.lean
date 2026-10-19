import InitECandidate.Runtime.HtabFreshTxFrame
import InitECandidate.Runtime.HtabLayoutBridge
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem discard_call_normal {F : Type} (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs ∧
      post.be = output.be ∧ post.code = output.code ∧ post.locals = state.locals := by
  rw [evaluateHOLFiniteState_call,args] at run
  simp only at run
  rw [lookup] at run
  simp only at run
  split at run
  · cases run
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result output =>
      rw [bodyRun] at run
      cases result with
      | none => cases run
      | some result =>
        cases result with
        | returned value =>
          simp only at run
          split at run
          · obtain ⟨_,rfl⟩ := Prod.mk.inj run
            exact ⟨value,output,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | finalFfi ffi => cases run
        | exception exceptionId value => cases run

/-- `htab_new(k, c)` as a discarded call: a fresh aligned empty table at the old heap pointer. -/
theorem htabNew_call_discardV {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength capacity pointer : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 14 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_new")
      [.const keyLength,.const capacity]) = (none,post)) :
    ∃ keys stride used values order orderPos : BitVec 64,
      HtabAligned keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat ∧
      OrderInv post capacity 0 used order orderPos ∧
      (∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
        orderPos.toNat + capacity.toNat * 8 ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const keyLength,.const capacity] = some [.val (.word keyLength),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨value,output,bodyRun,pm,pg,pa,pb,pc,_⟩ := discard_call_normal state post _ _ _ _ _ _ args
    (htabNew_installed state keyLength capacity code) run
  obtain ⟨keys,stride,used,values,order,orderPos,rfl,inv,kv,tables,_,_,_,p,hp,le,pal,pin⟩ := htabNew_returned_topV
    (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update
      (ofString "cap",.val (.word capacity)))) output _ keyLength capacity pointer bits (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap) pointerAligned pointerInside
    (fun a h1 h2 h3 => by exact arena a h1 h2 h3) power klenSmall (by change _ ≤ state.clock - 1; omega) bodyRun
  exact ⟨keys,stride,used,values,order,orderPos,inv.transfer pm pa pb pc,kv,tables.transfer pm pa pb,
    ⟨p,by rw [pg]; exact hp,le,pal,pin⟩⟩

#print axioms htabNew_call_discardV
set_option maxHeartbeats 8000000 in
theorem stateFreshTx_body_tables {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 379 ≤ s.clock) :
    ∃ Y : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_state_fresh_tx) =
        (some (.returned (.val (.word (0 : BitVec 64)))),
          {emptyLocalsHOLFinite Y with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite Y).locals (ofString "t",s.locals.lookup (ofString "t"))}) ∧
      (∀ a : BitVec 64, a.toNat < pointer.toNat → Y.memory a = s.memory a) ∧
      Y.memaddrs = s.memaddrs ∧ Y.be = s.be ∧ Y.code = s.code ∧
      (∃ P : BitVec 64, Y.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ pointer.toNat ≤ P.toNat ∧
        P.toNat % 8 = 0 ∧ P.toNat ≤ 33806089496) ∧
      Y.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "ts" → name ≠ ofString "journal_n" →
        Y.globals.lookup name = s.globals.lookup name) ∧
      s.clock ≤ Y.clock + 379 ∧ Y.clock ≤ s.clock ∧
      ∃ (T keys stride used values order orderPos : BitVec 64),
        pointer.toNat + 72 ≤ T.toNat ∧ Y.memory (pointer + BitVec.ofNat 64 8) = .word T ∧
        HtabAligned 20 T keys stride 64 used values order orderPos 0 6 Y ∧ OrderInv Y 64 0 used order orderPos ∧
        (∃ P : BitVec 64, Y.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧
          orderPos.toNat + 64 * 8 ≤ P.toNat) := by
  have e72 : (72 : BitVec 64).toNat = 72 := rfl
  have cov := allocationEnd_covers pointer 72 (by rw [e72]; omega)
  rw [e72] at cov
  have lim : (33806089496 : BitVec 64).toNat = 33806089496 := rfl
  obtain ⟨a1,arun,aclk,amem,alocals,acode,aaddrs,abe,ats,aheap,aglob⟩ := evaluate_alloc_global_call s (.const 72) pointer 72
    oldTs (ofString "ts") (by rw [evalListHOLFinite_eq_toExact]; rfl) code (by omega) heap tsGlobal (by decide)
    (by rw [BitVec.le_def,BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]; omega) (by omega)
  have hk : ∀ k : Nat, k < 72 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k :=
    fun k h => off_toNat pointer k (by omega) (by omega)
  have e0 : (pointer + 0).toNat = pointer.toNat := hk 0 (by omega)
  have e8 : (pointer + BitVec.ofNat 64 8).toNat = pointer.toNat + 8 := hk 8 (by omega)
  have bs1 : a1.globals.lookup (ofString "bs") = some (.val (.word B)) := by rw [aglob _ (by decide) (by decide)]; exact bsGlobal
  have dom1 : ∀ a : BitVec 64, a.toNat < 33806089496 → a1.memaddrs a := by rw [aaddrs]; exact domain
  have st0 := evaluate_store_word a1 (pointer + 0) B (.op .add [.var .global (ofString "ts"),.const 0])
    (.var .global (ofString "bs")) (eval_add2 a1 _ _ _ _ (eval_global_word a1 _ pointer ats) (item_eval_const a1 _))
    (eval_global_word a1 _ B bs1) (dom1 _ (by rw [e0]; omega))
  -- the first constructor, declared
  let s2 := sourceWriteWord a1 (pointer + 0) B
  obtain ⟨p1,hp1⟩ : ∃ x : BitVec 64, x = allocationEnd pointer 72 := ⟨_,rfl⟩
  rw [← hp1] at cov aheap
  have heap2 : s2.globals.lookup (ofString "heap_ptr") = some (.val (.word p1)) := aheap
  have code2 : s2.code = originalRuntimeCode := acode.trans code
  have dom2 : ∀ a : BitVec 64, a.toNat < 33806089496 → s2.memaddrs a := dom1
  have k20 : (20 : BitVec 64).toNat ≤ 52 := by decide
  have c64 : (64 : BitVec 64).toNat = 64 := rfl
  obtain ⟨_,hdrD,wordD,byteD⟩ := htabNew_heap_domains s2 p1 20 64 k20 (by rw [c64]; omega) dom2
  have args2 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a)) [.const 20,.const 64] =
      some [.val (.word 20),.val (.word 64)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨ready,rrun,_,rclk1,rclk2,rloc,rcode,raddr,rbe,rframe,decl⟩ :=
    evaluate_htabNew_call_and_declaration_before_header s2 _ _ p1 20 64 args2 code2 (by rw [c64]; change _ ≤ a1.clock; omega)
      heap2 k20 cov.2.2 (by rw [c64]; omega) hdrD wordD byteD
  obtain ⟨ready',rrun',_,_,_,_,_,_,_,rheap,_,_,_,_,_,_,_,_,_,rglob,_⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap_frame s2 _ _ p1 20 64 args2 code2
      (by rw [c64]; change _ ≤ a1.clock; omega) heap2 k20 cov.2.2 (by rw [c64]; omega) hdrD wordD byteD
  rw [rrun] at rrun'
  obtain ⟨_,rfl⟩ := Prod.mk.inj rrun'
  have bounds := stateFreshTx_next_table_bounds p1 20 64 (by decide) (by decide) (by omega)
  have p2eq : allocationEnd (htabNewOrderPos p1 20 64) (64 * 8) = stateFreshTxNextTable p1 20 64 := rfl
  rw [p2eq] at rheap
  obtain ⟨tk,tsd,tu,tv,tor,top,tinv,_,ttab,⟨tp,thp,tle,_,_⟩⟩ := htabNew_call_discardV s2 ready 20 64 p1 6 code2 heap2
    cov.2.2 (by omega) (fun a _ _ h => dom2 a h) (by rfl) (by decide) (by rw [c64]; change _ ≤ a1.clock; omega) rrun
  have tpEq : tp = stateFreshTxNextTable p1 20 64 := by
    rw [rheap] at thp; simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at thp; exact thp.symm
  subst tpEq
  rw [c64] at tle
  let s3 := setVarHOLFinite (ofString "t") (.val (.word p1)) ready
  have ts3 : s3.globals.lookup (ofString "ts") = some (.val (.word pointer)) := by
    change ready.globals.lookup _ = _; rw [rglob _ (by decide)]; exact ats
  have st8 := evaluate_store_word s3 (pointer + BitVec.ofNat 64 8) p1
    (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 8)]) (.var .local (ofString "t"))
    (eval_add2 s3 _ _ _ _ (eval_global_word s3 _ pointer ts3) (item_eval_const s3 _))
    (item_eval_locals s3 _ p1 (by simp [s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]))
    (by change ready.memaddrs _; rw [raddr]; exact dom2 _ (by rw [e8]; omega))
  let s4 := sourceWriteWord s3 (pointer + BitVec.ofNat 64 8) p1
  have rb := stateFreshTx_remaining_budgets
  have bc : blockClock stateFreshTxRemainingTables = 306 := by decide
  have clk4 : blockClock stateFreshTxRemainingTables ≤ s4.clock := by
    rw [bc]; change _ ≤ ready.clock; change a1.clock ≤ ready.clock + (64 : BitVec 64).toNat + 8 at rclk1
    rw [c64] at rclk1; omega
  obtain ⟨post5,P,run5,_,hP,alP,inP,leP,_,frame5,pc5,pa5,pb5,prel5,_,clk51,clk52⟩ :=
    recCtorSeq_run (ofString "ts") (by decide) pointer (.seq (.assign .global (ofString "journal_n") (.const 0))
      (.return (.const 0))) stateFreshTxRemainingTables s4 (stateFreshTxNextTable p1 20 64) p1 blockPlan_freshRemaining
      (by change ready.code = _; rw [rcode]; exact code2) ts3 rheap bounds.2.2
      (by intro a h; change ready.memaddrs a; rw [raddr]; exact dom2 a h) (by omega)
      (by rw [rb.1]; omega) clk4
      (by simp [s4,s3,sourceWriteWord,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  -- reset and return
  have glob5 : ∀ name, name ≠ ofString "heap_ptr" → post5.globals.lookup name = s4.globals.lookup name := prel5.1
  have cnt5 : post5.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)) := by
    rw [glob5 _ (by decide)]; change ready.globals.lookup _ = _; rw [rglob _ (by decide)]
    change a1.globals.lookup _ = _; rw [aglob _ (by decide) (by decide)]; exact counterGlobal
  let Y := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) post5
  have reset : evaluateHOLFiniteState post5 (.assign .global (ofString "journal_n") (.const 0)) = (none,Y) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,
      lookupKvarHOLExact,cnt5,Y]
  have finish : evaluateHOLFiniteState post5 (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite Y) := by
    rw [evaluateHOLFiniteState_seq_line780,reset]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have yglob : ∀ name, name ≠ ofString "journal_n" → Y.globals.lookup name = post5.globals.lookup name := by
    intro name h; simp [Y,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm h]
  have mem5 : ∀ a : BitVec 64, a.toNat < pointer.toNat → post5.memory a = s.memory a := by
    intro a lt
    have n0 : a ≠ pointer + 0 := fun e => by rw [e,e0] at lt; omega
    have n8 : a ≠ pointer + BitVec.ofNat 64 8 := fun e => by rw [e,e8] at lt; omega
    rw [frame5 a (by omega) (fun o m e => by
      have ob := BlockPlan.offsets _ blockPlan_freshRemaining o m
      rw [e,off_toNat pointer o (by omega) (by omega)] at lt; omega)]
    change (if a = pointer + BitVec.ofNat 64 8 then _ else s3.memory a) = _
    rw [if_neg n8]
    change ready.memory a = _
    rw [rframe a (by omega)]
    change (if a = pointer + 0 then _ else a1.memory a) = _
    rw [if_neg n0,amem]
  have keepT : ∀ a : BitVec 64, a.toNat < (stateFreshTxNextTable p1 20 64).toNat → p1.toNat ≤ a.toNat →
      post5.memory a = ready.memory a := by
    intro a lt ge
    have c1 := cov.1
    rw [frame5 a lt (fun o m e => by
      have ob := BlockPlan.offsets _ blockPlan_freshRemaining o m
      have o64 : o ≤ 64 := by simp [stateFreshTxRemainingTables] at m; omega
      rw [e,off_toNat pointer o (by omega) (by omega)] at ge; omega)]
    have n8 : a ≠ pointer + BitVec.ofNat 64 8 := fun e => by
      have h8 := e8; rw [← e] at h8; omega
    change (if a = pointer + BitVec.ofNat 64 8 then _ else s3.memory a) = _
    rw [if_neg n8]
    rfl
  have tblY := tinv.keep_block (r := Y) ttab (by change post5.memaddrs = _; rw [pa5]; rfl)
    (by change post5.be = _; rw [pb5]; rfl) (by change post5.code = _; rw [pc5]; rfl)
    (fun a lo hi => by change post5.memory a = _; rw [c64] at hi; exact keepT a (by omega) lo)
  have cellY : Y.memory (pointer + BitVec.ofNat 64 8) = .word p1 := by
    change post5.memory _ = _
    rw [frame5 _ (by rw [e8]; omega) (fun o m e => by
      have ob := BlockPlan.offsets _ blockPlan_freshRemaining o m
      have e' := congrArg BitVec.toNat e
      rw [e8,off_toNat pointer o (by omega) (by omega)] at e'
      have : o = 8 := by omega
      subst this; revert m; decide)]
    change (if pointer + BitVec.ofNat 64 8 = pointer + BitVec.ofNat 64 8 then HolWordLab.word p1 else _) = _
    rw [if_pos rfl]
  refine ⟨Y,?_,mem5,pa5.trans (raddr.trans aaddrs),pb5.trans (rbe.trans abe),
    pc5.trans (rcode.trans (acode)),⟨P,by rw [yglob _ (by decide)]; exact hP,by omega,alP,inP⟩,?_,?_,?_,?_,
    ⟨p1,tk,tsd,tu,tv,tor,top,by omega,cellY,tblY.1,tblY.2,⟨P,by rw [yglob _ (by decide)]; exact hP,
      by omega⟩⟩⟩
  · rw [source_stateFreshTx_body,evaluateHOLFiniteState_seq_line780,arun]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780,st0]; dsimp only
    rw [decl]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780]
    unfold stateFreshTxPointerStore
    rw [st8]; dsimp only
    rw [stateFreshTxConstructorSequence_eq,run5,finish]
    have l2 : s2.locals = s.locals := alocals
    rw [l2]
  · rw [yglob _ (by decide),glob5 _ (by decide)]; exact ts3
  · intro name h1 h2 h3
    rw [yglob _ h3,glob5 _ h1]; change ready.globals.lookup _ = _; rw [rglob _ h1]; exact aglob name h2 h1
  · change s.clock ≤ post5.clock + 379
    have h4 : s4.clock = ready.clock := rfl
    have h2 : s2.clock = a1.clock := rfl
    rw [bc] at clk51
    rw [c64] at rclk1
    omega
  · change post5.clock ≤ s.clock
    have h4 : s4.clock = ready.clock := rfl
    have h2 : s2.clock = a1.clock := rfl
    omega

#print axioms stateFreshTx_body_tables

set_option maxHeartbeats 4000000 in
theorem stateFreshTx_call_tables {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 380 ≤ s.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      (∀ a : BitVec 64, a.toNat < pointer.toNat → post.memory a = s.memory a) ∧
      post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      (∃ P : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ pointer.toNat ≤ P.toNat ∧
        P.toNat % 8 = 0 ∧ P.toNat ≤ 33806089496) ∧
      post.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "ts" → name ≠ ofString "journal_n" →
        post.globals.lookup name = s.globals.lookup name) ∧
      s.clock ≤ post.clock + 380 ∧ post.clock ≤ s.clock ∧
      ∃ (T keys stride used values order orderPos : BitVec 64),
        pointer.toNat + 72 ≤ T.toNat ∧ post.memory (pointer + BitVec.ofNat 64 8) = .word T ∧
        HtabAligned 20 T keys stride 64 used values order orderPos 0 6 post ∧ OrderInv post 64 0 used order orderPos ∧
        (∃ P : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧
          orderPos.toNat + 64 * 8 ≤ P.toNat) := by
  let E := callEntryStateHOLFinite s HolFiniteMapExact.empty
  obtain ⟨Y,body,mem,ma,mb,mc,hP,hts,glob,clk1,clk2,T,k,st,u,v,o,op,tl,tc,ti,tt,tP⟩ := stateFreshTx_body_tables E pointer oldTs B oldCount
    (by exact code) (by exact heap) (by exact tsGlobal) (by exact bsGlobal) (by exact counterGlobal) reservation
    (by exact domain) (by change 379 ≤ s.clock - 1; omega)
  have lookup := pan_no_args_lookup s.code.lookup (ofString "state_fresh_tx")
    (sourceFunctionBody Guest.guestFn_state_fresh_tx) (by rw [code]; exact originalRuntimeCode_stateFreshTx_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals s none (ofString "state_fresh_tx") [] []
    (sourceFunctionBody Guest.guestFn_state_fresh_tx) HolFiniteMapExact.empty .one (.val (.word (0 : BitVec 64))) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,fun a h => mem a h,rfl,ma,mb,mc,hP,hts,glob,?_,?_,T,k,st,u,v,o,op,tl,tc,ti.transfer rfl rfl rfl rfl,
    tt.transfer rfl rfl rfl,tP⟩
  · change s.clock ≤ Y.clock + 380; change s.clock - 1 ≤ Y.clock + 379 at clk1; omega
  · change Y.clock ≤ s.clock; change Y.clock ≤ s.clock - 1 at clk2; omega

#print axioms stateFreshTx_call_tables
end InitECandidate.Runtime
