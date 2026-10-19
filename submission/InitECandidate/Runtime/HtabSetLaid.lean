import InitECandidate.Runtime.HtabDescending
import InitECandidate.Runtime.VmFn_htab_item
import InitECandidate.Runtime.PanTailCallBodyFrame
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! Hash-table operations on actual layouts (aligned heap tables and descending scratch
tables): the `htab_item`/`htab_slot` reads, and `htab_set` with its exact footprint (header
plus current array block), capacity growth bound and array placement. -/

theorem source_htabItem_body : sourceFunctionBody Guest.guestFn_htab_item =
    .dec (ofString "i") .one (.load .one (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 56]),
      .panop .mul [.var .local (ofString "ordinal"),.const 8]]))
      (.call none (ofString "htab_slot") [.var .local (ofString "t"),.var .local (ofString "i")]) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_htabSlot_body : sourceFunctionBody Guest.guestFn_htab_slot =
    .dec (ofString "used") .one (.loadByte (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 48]),
      .var .local (ofString "i")]))
    (.dec (ofString "keyp") .one (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 32]),
      .panop .mul [.var .local (ofString "i"),.load .one (.op .add [.var .local (ofString "t"),.const 8])]])
    (.dec (ofString "val") .one (.load .one (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 40]),
      .panop .mul [.var .local (ofString "i"),.const 8]]))
    (.return (.rstruct [.var .local (ofString "used"),.var .local (ofString "keyp"),.var .local (ofString "val")])))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A successful one-word load from a word address reads that memory cell. -/
theorem eval_load_word_some {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (a : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e = some (.val (.word a)))
    (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one e) = some v) :
    v = .val (s.memory a) := by
  simp only [evalHOLExact,isWfShapeExactHOL,he,memLoadHOLExact] at h
  split at h
  · simp at h; exact h.2.symm
  · simp at h

#print axioms eval_load_word_some

theorem item_eval_locals {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (w : BitVec 64)
    (h : s.locals.lookup name = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.var .local name) =
      some (.val (.word w)) := by
  simpa [evalHOLExact] using h

theorem eval_loadByte_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) = some v) :
    ∃ b : BitVec 64, v = .val (.word b) := by
  simp only [evalHOLExact] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x,_,rfl⟩ := h
    exact ⟨_,rfl⟩
  · simp at h

theorem eval_add2 {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : ExpHOL 64) (a b : BitVec 64)
    (hA : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) A = some (.val (.word a)))
    (hB : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) B = some (.val (.word b))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.op .add [A,B]) =
      some (.val (.word (a + b))) := by
  simp [evalHOLExact,evalListHOLExact,hA,hB,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem eval_mul2 {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : ExpHOL 64) (a b : BitVec 64)
    (hA : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) A = some (.val (.word a)))
    (hB : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) B = some (.val (.word b))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.panop .mul [A,B]) =
      some (.val (.word (a * b))) := by
  simp [evalHOLExact,evalListHOLExact,hA,hB,valueIsWord,valueWord,panOpHOL]

theorem item_eval_const {F : Type} (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.const k) = some (.val (.word k)) := rfl

theorem eval_load_word {F : Type} (s : PanSemStateFiniteExact 64 F) (A : ExpHOL 64) (a w : BitVec 64)
    (hA : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) A = some (.val (.word a)))
    (dom : s.memaddrs a) (cell : s.memory a = .word w) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one A) = some (.val (.word w)) := by
  simp [evalHOLExact,isWfShapeExactHOL,hA,memLoadHOLExact,dom,cell]

/-- htab_slot returns the used byte, the key pointer and the value word of slot i. -/
theorem htabSlot_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (w : ValueHOL 64)
    (table slot keys stride values vv : BitVec 64)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (iL : s.locals.lookup (ofString "i") = some (.val (.word slot)))
    (d32 : s.memaddrs (table + 32)) (c32 : s.memory (table + 32) = .word keys)
    (d8 : s.memaddrs (table + 8)) (c8 : s.memory (table + 8) = .word stride)
    (d40 : s.memaddrs (table + 40)) (c40 : s.memory (table + 40) = .word values)
    (dVal : s.memaddrs (values + slot * 8)) (cVal : s.memory (values + slot * 8) = .word vv)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_slot) = (some (.returned w),post)) :
    ∃ b : BitVec 64, w = .rStruct [.val (.word b),.val (.word (keys + slot * stride)),.val (.word vv)] := by
  rw [source_htabSlot_body] at run
  obtain ⟨uv,r1,e1,run1,_⟩ := dec_returned_state run
  obtain ⟨b,rfl⟩ := eval_loadByte_word s _ uv e1
  generalize h1 : setVarHOLFinite (ofString "used") (.val (.word b)) s = s1 at run1
  have s1t : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← h1]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tL]
  have s1i : s1.locals.lookup (ofString "i") = some (.val (.word slot)) := by
    rw [← h1]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,iL]
  have s1u : s1.locals.lookup (ofString "used") = some (.val (.word b)) := by
    rw [← h1]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have s1m : s1.memory = s.memory ∧ s1.memaddrs = s.memaddrs := by rw [← h1]; exact ⟨rfl,rfl⟩
  obtain ⟨kv,r2,e2,run2,_⟩ := dec_returned_state run1
  rw [eval_add2 s1 _ _ keys (slot * stride)
    (eval_load_word s1 _ (table + 32) keys (eval_add2 s1 _ _ table 32 (item_eval_locals s1 _ _ s1t) (item_eval_const s1 32))
      (by rw [s1m.2]; exact d32) (by rw [s1m.1]; exact c32))
    (eval_mul2 s1 _ _ slot stride (item_eval_locals s1 _ _ s1i)
      (eval_load_word s1 _ (table + 8) stride (eval_add2 s1 _ _ table 8 (item_eval_locals s1 _ _ s1t) (item_eval_const s1 8))
        (by rw [s1m.2]; exact d8) (by rw [s1m.1]; exact c8)))] at e2
  cases e2
  generalize h2 : setVarHOLFinite (ofString "keyp") (.val (.word (keys + slot * stride))) s1 = s2 at run2
  have s2t : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← h2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,s1t]
  have s2i : s2.locals.lookup (ofString "i") = some (.val (.word slot)) := by
    rw [← h2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,s1i]
  have s2u : s2.locals.lookup (ofString "used") = some (.val (.word b)) := by
    rw [← h2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,s1u]
  have s2k : s2.locals.lookup (ofString "keyp") = some (.val (.word (keys + slot * stride))) := by
    rw [← h2]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have s2m : s2.memory = s.memory ∧ s2.memaddrs = s.memaddrs := by rw [← h2]; exact s1m
  obtain ⟨vv',r3,e3,run3,_⟩ := dec_returned_state run2
  rw [eval_load_word s2 _ (values + slot * 8) vv
    (eval_add2 s2 _ _ values (slot * 8)
      (eval_load_word s2 _ (table + 40) values (eval_add2 s2 _ _ table 40 (item_eval_locals s2 _ _ s2t) (item_eval_const s2 40))
        (by rw [s2m.2]; exact d40) (by rw [s2m.1]; exact c40))
      (eval_mul2 s2 _ _ slot 8 (item_eval_locals s2 _ _ s2i) (item_eval_const s2 8)))
    (by rw [s2m.2]; exact dVal) (by rw [s2m.1]; exact cVal)] at e3
  cases e3
  generalize h3 : setVarHOLFinite (ofString "val") (.val (.word vv)) s2 = s3 at run3
  have s3u : s3.locals.lookup (ofString "used") = some (.val (.word b)) := by
    rw [← h3]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,s2u]
  have s3k : s3.locals.lookup (ofString "keyp") = some (.val (.word (keys + slot * stride))) := by
    rw [← h3]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,s2k]
  have s3v : s3.locals.lookup (ofString "val") = some (.val (.word vv)) := by
    rw [← h3]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [evaluateHOLFiniteState_return] at run3
  have ev : @evalHOLExact 64 F _ s3.toExact (fun x => Classical.propDecidable (s3.memaddrs x))
      (.rstruct [.var .local (ofString "used"),.var .local (ofString "keyp"),.var .local (ofString "val")]) =
      some (.rStruct [.val (.word b),.val (.word (keys + slot * stride)),.val (.word vv)]) := by
    simp [evalHOLExact,evalListHOLExact,s3u,s3k,s3v]
  rw [ev] at run3
  dsimp only at run3
  split at run3
  · obtain ⟨e,_⟩ := Prod.mk.inj run3
    simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
    exact ⟨b,e.symm⟩
  · simp at run3

/-- htab_item returns the used byte, key pointer and value word of the slot recorded at order[ordinal]. -/
theorem htabItem_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (w : ValueHOL 64)
    (table ordinal order slot keys stride values vv : BitVec 64) (code : s.code = originalRuntimeCode)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (oL : s.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (d56 : s.memaddrs (table + 56)) (c56 : s.memory (table + 56) = .word order)
    (dOrd : s.memaddrs (order + ordinal * 8)) (cOrd : s.memory (order + ordinal * 8) = .word slot)
    (d32 : s.memaddrs (table + 32)) (c32 : s.memory (table + 32) = .word keys)
    (d8 : s.memaddrs (table + 8)) (c8 : s.memory (table + 8) = .word stride)
    (d40 : s.memaddrs (table + 40)) (c40 : s.memory (table + 40) = .word values)
    (dVal : s.memaddrs (values + slot * 8)) (cVal : s.memory (values + slot * 8) = .word vv)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_item) = (some (.returned w),post)) :
    ∃ b : BitVec 64, w = .rStruct [.val (.word b),.val (.word (keys + slot * stride)),.val (.word vv)] := by
  rw [source_htabItem_body] at run
  obtain ⟨iv,r1,e1,run1,_⟩ := dec_returned_state run
  rw [eval_load_word s _ (order + ordinal * 8) slot
    (eval_add2 s _ _ order (ordinal * 8)
      (eval_load_word s _ (table + 56) order (eval_add2 s _ _ table 56 (item_eval_locals s _ _ tL) (item_eval_const s 56))
        d56 c56)
      (eval_mul2 s _ _ ordinal 8 (item_eval_locals s _ _ oL) (item_eval_const s 8)))
    dOrd cOrd] at e1
  cases e1
  generalize h1 : setVarHOLFinite (ofString "i") (.val (.word slot)) s = s1 at run1
  have s1t : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← h1]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tL]
  have s1i : s1.locals.lookup (ofString "i") = some (.val (.word slot)) := by
    rw [← h1]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have s1m : s1.memory = s.memory ∧ s1.memaddrs = s.memaddrs ∧ s1.code = s.code := by rw [← h1]; exact ⟨rfl,rfl,rfl⟩
  have args : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "i")] = some [.val (.word table),.val (.word slot)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,s1t,s1i]
  have lookup := pan_two_word_lookup_shape s1.code.lookup (ofString "htab_slot") (ofString "t") (ofString "i")
    (sourceFunctionBody Guest.guestFn_htab_slot) (.comb [.one,.one,.one]) table slot (by decide)
    (by rw [s1m.2.2,code]; exact vmLookup_htab_slot)
  rw [evaluateHOLFiniteState_call,args] at run1
  dsimp only at run1
  rw [lookup] at run1
  dsimp only at run1
  split at run1
  · simp at run1
  · generalize hentry : callEntryStateHOLFinite s1
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "i",.val (.word slot))) = entry at run1
    have eT : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
      rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have eI : entry.locals.lookup (ofString "i") = some (.val (.word slot)) := by
      rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have eM : entry.memory = s.memory ∧ entry.memaddrs = s.memaddrs := by
      rw [← hentry]; exact ⟨s1m.1,s1m.2.1⟩
    cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_slot) with
    | mk r p =>
      rw [bodyRun] at run1
      rcases r with _ | (_ | _ | _ | _ | w' | _ | _)
      all_goals first
        | (simp at run1; done)
        | skip
      dsimp only at run1
      split at run1
      · obtain ⟨e,_⟩ := Prod.mk.inj run1
        simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
        subst e
        exact htabSlot_returned entry p w' table slot keys stride values vv eT eI
          (by rw [eM.2]; exact d32) (by rw [eM.1]; exact c32) (by rw [eM.2]; exact d8) (by rw [eM.1]; exact c8)
          (by rw [eM.2]; exact d40) (by rw [eM.1]; exact c40) (by rw [eM.2]; exact dVal) (by rw [eM.1]; exact cVal) bodyRun
      · simp at run1
#print axioms htabSlot_returned
#print axioms htabItem_returned

set_option maxHeartbeats 1000000 in
/-- Set on an aligned table, with the fine frame (header and current array block only), the capacity bound
and the array layout outcome (unchanged arrays, or fresh arrays at or above the heap pointer). -/
theorem htabSet_returned_fine {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned v),post)) :
    ∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      ((capacity' = capacity ∧ keys' = keys ∧ values' = values ∧ orderPos' = orderPos) ∨
        (pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat)) ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        ((w.toNat < keys.toNat ∧ w.toNat < values.toNat) ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
  rw [source_htabSet_body] at run
  obtain ⟨values0,body,callee,rs,w,bodyPost,r,inner,args,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc⟩ := decCall_returned_globals run
  have argsExact : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  rw [argsExact] at args
  cases args
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry at bodyRun rclk
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  have entryT : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨wi,rfl,wiLe⟩ := htabFindSlot_returned_range entry bodyPost table capacity bits entryInv.power entryT
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 w bodyRun
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  have findBound := evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used
    empty bits entryT
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
    entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
    (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
    entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
    (by rw [entryFacts.2.2.2.2.2]; omega)
  unfold RunBounded at findBound
  rw [bodyRun] at findBound
  obtain ⟨fb1,fb2,_⟩ := findBound
  dsimp only at fb1 fb2
  have frame := htabFindSlot_memoryFrame entry entryInv.code
  have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
  rw [bodyRun] at frame meta'
  have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
      r.globals = state.globals ∧ state.clock ≤ r.clock + (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) + 1 :=
    ⟨rm.trans (frame.1.trans entryFacts.1),ra.trans (meta'.2.1.trans entryFacts.2.1),rb.trans (meta'.2.2.1.trans entryFacts.2.2.1),
      rc.trans (meta'.1.trans entryFacts.2.2.2.1),rg.trans (frame.2.trans entryFacts.2.2.2.2.1),
      by rw [rclk fb2]; have := entryFacts.2.2.2.2.2; omega⟩
  have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
  have rTables := tables.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1
  have rT := (ragree _ (by decide)).trans tableLocal
  have rKey := (ragree _ (by decide)).trans keyLocal
  have rValue := (ragree _ (by decide)).trans valueLocal
  rw [evaluateHOLFiniteState_seq_line780] at rrun
  cases upd : evaluateHOLFiniteState r htabSetUpdate with
  | mk ur u =>
    rw [upd] at rrun
    cases ur with
    | some ur =>
      -- existing key: value cell written, then return
      obtain ⟨e,rfl⟩ := Prod.mk.inj rrun
      simp only [Option.some.injEq] at e
      subst e
      obtain ⟨lt,um,ua,ub,uc⟩ := htabSetUpdate_returned r u v table capacity values wi value rT rh rValue wiLe
        (by exact rInv.header_domain 16 (by omega) (by omega)) (by exact rInv.cell16)
        (by exact rInv.header_domain 40 (by omega) (by omega)) (by exact rInv.cell40) upd
      have hv := rInv.headerValues
      have vb := rInv.valuesBefore
      have written := rInv.write_outside (values + wi * 8) value
        (fun k hk => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            word_add_toNat table k (by have := keys.isLt; have := rInv.headerKeys; omega)]
          change ¬(_ + _ * 8 = _); omega))
        (fun slot inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.usedBefore; have := rInv.orderBefore; have := rInv.endBound; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
      have writtenTables := rTables.write_far rInv (values + wi * 8) value
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.usedBefore; have := rInv.orderBefore; have := rInv.endBound; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.2.1]
          have := rInv.usedBefore; have := rInv.orderBefore
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.1]
          have := rInv.usedBefore; have := rInv.orderBefore
          change ¬(_ + _ * 8 = _); omega))
      refine ⟨capacity,keys,used,values,order,orderPos,count,bits,
        written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc),Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1),
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub),Or.inl rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩,
        fun w _ _ fine => by
          rw [pm,um]
          simp only [sourceWriteWord]
          rw [if_neg (word_ne_of_toNat (by
            rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega)]
            have := rInv.usedBefore; have := rInv.orderBefore
            change ¬(_ = _ + _ * 8); rcases fine with ⟨f1,f2⟩ | f3 <;> omega))]
          exact rFacts.1 ▸ rfl⟩
    | none =>
      have same := htabSetUpdate_normal r u upd
      subst same
      simp only at rrun
      have capDouble : (capacity * 2).toNat = capacity.toNat * 2 :=
        BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
      have countOne : (count + 1).toNat = count.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
      have growArgs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
          [.var .local (ofString "t")] = some [.val (.word table)] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rT]
      have insArgs : ∀ g : PanSemStateFiniteExact 64 F, g.locals = u.locals →
          evalListHOLFinite g (h := fun a => Classical.propDecidable (g.memaddrs a))
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
            some [.val (.word table),.val (.word key),.val (.word value)] := by
        intro g gl
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,gl,rT,rKey,rValue]
      -- the insertion and final return from the state after the growth guard
      have finish : ∀ (g : PanSemStateFiniteExact 64 F) (capacity' keys' used' values' order' orderPos' : BitVec 64)
          (bits' : Nat),
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count bits' g →
          OrderInv g capacity' count used' order' orderPos' →
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' ∧
            (∀ w : BitVec 64, w ≠ table + 24 → ((w.toNat < keys'.toNat ∧ w.toNat < values'.toNat) ∨
              orderPos'.toNat + capacity'.toNat * 8 ≤ w.toNat) → inner.memory w = g.memory w) := by
        intro g capacity' keys' used' values' order' orderPos' bits' gInv gTables gl roomG gClock gRun
        rw [evaluateHOLFiniteState_seq_line780] at gRun
        cases insRun : evaluateHOLFiniteState g (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) with
        | mk ir ins =>
          rw [insRun] at gRun
          cases ir with
          | some ir =>
            exfalso
            obtain ⟨e,_⟩ := Prod.mk.inj gRun
            simp only [Option.some.injEq] at e
            subst e
            exact discard_call_not_returned g _ _ v (by rw [insRun])
          | none =>
            simp only at gRun
            obtain ⟨insInv,_,insAddr,insBe,_⟩ := htabInsertRaw_call_normal_aligned g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨insTables,insFine⟩ := htabInsertRaw_call_normal_fine g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb,
              fun w n24 far => by rw [em]; exact insFine w n24 far⟩
      rw [evaluateHOLFiniteState_seq_line780] at rrun
      cases gRun : evaluateHOLFiniteState u (.ite htabSetGuard
          (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) with
      | mk gr g =>
        rw [gRun] at rrun
        cases gr with
        | some gr =>
          exfalso
          obtain ⟨e,_⟩ := Prod.mk.inj rrun
          simp only [Option.some.injEq] at e
          subst e
          rw [evaluateHOLFiniteState_ite] at gRun
          split at gRun
          · split at gRun
            · simp [evaluateHOLFiniteState_skip] at gRun
            · exact discard_call_not_returned u _ _ v (by rw [gRun])
          · simp at gRun
        | none =>
          simp only at rrun
          have guardVal := eval_htabSetGuard u table capacity count rT (by exact rInv.header_domain 16 (by omega) (by omega))
            (by exact rInv.cell16) (by exact rInv.header_domain 24 (by omega) (by omega)) (by exact rInv.cell24) (by omega)
          rcases ite_normal_cases_cond u g _ _ _ gRun with ⟨gw,gnz,gcond,grown⟩ | ⟨gcond,skipped⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have over : capacity.toNat < (count.toNat + 1) * 2 := by
              by_cases h : capacity.toNat < (count.toNat + 1) * 2
              · exact h
              · simp [h] at gcond; exact absurd gcond.symm gnz
            obtain ⟨⟨k',u',v',o',op',gInv,gTables,kLe,vLe⟩,gLocals,gAddr,gBe,gFrame⟩ := htabGrow_call_normal_frame u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have growB := runBounded_htabGrow_call u _ keyLength table keys stride capacity used values order orderPos count
              pointer bits rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
              (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by have := rFacts.2.2.2.2.2; omega)
            unfold RunBounded at growB
            rw [grown] at growB
            obtain ⟨gb1,_,_⟩ := growB
            dsimp only at gb1
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gTables gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb,Or.inr (by rw [capDouble,countOne]; omega),Or.inr ⟨kLe,vLe⟩,fun w below hdr _ => by
                have := rInv.headerKeys; have := rInv.keysBefore; have := rInv.usedBefore; have := rInv.orderBefore
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (Or.inl ⟨by omega,by omega⟩),
                  gFrame w below hdr,rFacts.1]⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish u capacity keys used values order orderPos bits rInv rTables rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb,
              Or.inl rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩,fun w _ hdr fine => by
                have := rInv.headerKeys; have := rInv.headerValues; have := rInv.keysBefore; have := rInv.usedBefore
                have := rInv.orderBefore
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) fine,rFacts.1]⟩

#print axioms htabSet_returned_fine

set_option maxHeartbeats 2000000 in
/-- Set on a descending scratch table: either it stays descending with the same arrays, or it grew into an
aligned table whose fresh arrays lie at or above the heap pointer; with the capacity bound. -/
theorem htabSet_returned_desc_fine {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned v),post)) :
    ∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      ((HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
          capacity' = capacity ∧ keys' = keys ∧ values' = values ∧ orderPos' = orderPos) ∨
        (HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
          pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat)) ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < orderPos.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.orderBelow; have := inv.orderPosBelow; have := inv.tableEnd; omega
  rw [source_htabSet_body] at run
  obtain ⟨values0,body,callee,rs,w,bodyPost,r,inner,args,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc⟩ := decCall_returned_globals run
  have argsExact : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  rw [argsExact] at args
  cases args
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry at bodyRun rclk
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  have entryT : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨wi,rfl,wiLe⟩ := htabFindSlot_returned_range entry bodyPost table capacity bits entryInv.power entryT
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 w bodyRun
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  have findBound := evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used
    empty bits entryT
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
    entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
    (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
    entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
    (by rw [entryFacts.2.2.2.2.2]; omega)
  unfold RunBounded at findBound
  rw [bodyRun] at findBound
  obtain ⟨fb1,fb2,_⟩ := findBound
  dsimp only at fb1 fb2
  have frame := htabFindSlot_memoryFrame entry entryInv.code
  have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
  rw [bodyRun] at frame meta'
  have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
      r.globals = state.globals ∧ state.clock ≤ r.clock + (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) + 1 :=
    ⟨rm.trans (frame.1.trans entryFacts.1),ra.trans (meta'.2.1.trans entryFacts.2.1),rb.trans (meta'.2.2.1.trans entryFacts.2.2.1),
      rc.trans (meta'.1.trans entryFacts.2.2.2.1),rg.trans (frame.2.trans entryFacts.2.2.2.2.1),
      by rw [rclk fb2]; have := entryFacts.2.2.2.2.2; omega⟩
  have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
  have rTables := tables.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1
  have rT := (ragree _ (by decide)).trans tableLocal
  have rKey := (ragree _ (by decide)).trans keyLocal
  have rValue := (ragree _ (by decide)).trans valueLocal
  rw [evaluateHOLFiniteState_seq_line780] at rrun
  cases upd : evaluateHOLFiniteState r htabSetUpdate with
  | mk ur u =>
    rw [upd] at rrun
    cases ur with
    | some ur =>
      -- existing key: value cell written, then return
      obtain ⟨e,rfl⟩ := Prod.mk.inj rrun
      simp only [Option.some.injEq] at e
      subst e
      obtain ⟨lt,um,ua,ub,uc⟩ := htabSetUpdate_returned r u v table capacity values wi value rT rh rValue wiLe
        (by exact rInv.header_domain 16 (by omega) (by omega)) (by exact rInv.cell16)
        (by exact rInv.header_domain 40 (by omega) (by omega)) (by exact rInv.cell40) upd
      have hv := rInv.valuesBelow
      have vb := rInv.usedBelow
      have written := rInv.write_outside (values + wi * 8) value
        (fun k hk => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            word_add_toNat table k (by have := keys.isLt; have := rInv.keysBelow; omega)]
          change ¬(_ + _ * 8 = _); omega))
        (fun slot inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.orderBelow; have := rInv.orderPosBelow; have := rInv.tableEnd; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
      have writtenTables := rTables.write_far_desc rInv (values + wi * 8) value
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.orderBelow; have := rInv.orderPosBelow; have := rInv.tableEnd; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.2.1]
          have := rInv.orderBelow; have := rInv.orderPosBelow
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.1]
          have := rInv.orderBelow; have := rInv.orderPosBelow
          change ¬(_ + _ * 8 = _); omega))
      refine ⟨capacity,keys,used,values,order,orderPos,count,bits,
        Or.inl ⟨written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc),rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1),
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub),Or.inl rfl,fun w _ outside => by
          rw [pm,um]
          simp only [sourceWriteWord]
          rw [if_neg (word_ne_of_toNat (by
            rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega)]
            have := rInv.orderBelow; have := rInv.orderPosBelow
            change ¬(_ = _ + _ * 8); omega))]
          exact rFacts.1 ▸ rfl⟩
    | none =>
      have same := htabSetUpdate_normal r u upd
      subst same
      simp only at rrun
      have capDouble : (capacity * 2).toNat = capacity.toNat * 2 :=
        BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
      have countOne : (count + 1).toNat = count.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
      have growArgs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
          [.var .local (ofString "t")] = some [.val (.word table)] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rT]
      have insArgs : ∀ g : PanSemStateFiniteExact 64 F, g.locals = u.locals →
          evalListHOLFinite g (h := fun a => Classical.propDecidable (g.memaddrs a))
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
            some [.val (.word table),.val (.word key),.val (.word value)] := by
        intro g gl
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,gl,rT,rKey,rValue]
      -- the insertion and final return from the state after the growth guard
      have finish : ∀ (g : PanSemStateFiniteExact 64 F) (capacity' keys' used' values' order' orderPos' : BitVec 64)
          (bits' : Nat),
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count bits' g →
          OrderInv g capacity' count used' order' orderPos' →
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' ∧
            (∀ w : BitVec 64, w ≠ table + 24 → ((w.toNat < keys'.toNat ∧ w.toNat < values'.toNat) ∨
              orderPos'.toNat + capacity'.toNat * 8 ≤ w.toNat) → inner.memory w = g.memory w) := by
        intro g capacity' keys' used' values' order' orderPos' bits' gInv gTables gl roomG gClock gRun
        rw [evaluateHOLFiniteState_seq_line780] at gRun
        cases insRun : evaluateHOLFiniteState g (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) with
        | mk ir ins =>
          rw [insRun] at gRun
          cases ir with
          | some ir =>
            exfalso
            obtain ⟨e,_⟩ := Prod.mk.inj gRun
            simp only [Option.some.injEq] at e
            subst e
            exact discard_call_not_returned g _ _ v (by rw [insRun])
          | none =>
            simp only at gRun
            obtain ⟨insInv,_,insAddr,insBe,_⟩ := htabInsertRaw_call_normal_aligned g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨insTables,insFine⟩ := htabInsertRaw_call_normal_fine g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb,
              fun w n24 far => by rw [em]; exact insFine w n24 far⟩
      have finishD : ∀ (g : PanSemStateFiniteExact 64 F) (capacity' keys' used' values' order' orderPos' : BitVec 64)
          (bits' : Nat),
          HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count bits' g →
          OrderInv g capacity' count used' order' orderPos' →
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' ∧
            (∀ w : BitVec 64, w ≠ table + 24 → (w.toNat < orderPos'.toNat ∨
              keys'.toNat + capacity'.toNat * stride.toNat ≤ w.toNat) → inner.memory w = g.memory w) := by
        intro g capacity' keys' used' values' order' orderPos' bits' gInv gTables gl roomG gClock gRun
        rw [evaluateHOLFiniteState_seq_line780] at gRun
        cases insRun : evaluateHOLFiniteState g (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) with
        | mk ir ins =>
          rw [insRun] at gRun
          cases ir with
          | some ir =>
            exfalso
            obtain ⟨e,_⟩ := Prod.mk.inj gRun
            simp only [Option.some.injEq] at e
            subst e
            exact discard_call_not_returned g _ _ v (by rw [insRun])
          | none =>
            simp only at gRun
            obtain ⟨insInv,insAddr,insBe,insTables,insFine⟩ := htabInsertRaw_call_normal_desc g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb,
              fun w n24 far => by rw [em]; exact insFine w n24 far⟩
      rw [evaluateHOLFiniteState_seq_line780] at rrun
      cases gRun : evaluateHOLFiniteState u (.ite htabSetGuard
          (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) with
      | mk gr g =>
        rw [gRun] at rrun
        cases gr with
        | some gr =>
          exfalso
          obtain ⟨e,_⟩ := Prod.mk.inj rrun
          simp only [Option.some.injEq] at e
          subst e
          rw [evaluateHOLFiniteState_ite] at gRun
          split at gRun
          · split at gRun
            · simp [evaluateHOLFiniteState_skip] at gRun
            · exact discard_call_not_returned u _ _ v (by rw [gRun])
          · simp at gRun
        | none =>
          simp only at rrun
          have guardVal := eval_htabSetGuard u table capacity count rT (by exact rInv.header_domain 16 (by omega) (by omega))
            (by exact rInv.cell16) (by exact rInv.header_domain 24 (by omega) (by omega)) (by exact rInv.cell24) (by omega)
          rcases ite_normal_cases_cond u g _ _ _ gRun with ⟨gw,gnz,gcond,grown⟩ | ⟨gcond,skipped⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have over : capacity.toNat < (count.toNat + 1) * 2 := by
              by_cases h : capacity.toNat < (count.toNat + 1) * 2
              · exact h
              · simp [h] at gcond; exact absurd gcond.symm gnz
            obtain ⟨⟨k',u',v',o',op',gInv,gTables,kLe,vLe⟩,gLocals,gAddr,gBe,gFrame⟩ := htabGrow_call_normal_frame_regions u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have growB := runBounded_htabGrow_call_regions u _ keyLength table keys stride capacity used values order orderPos count
              pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
              (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by have := rFacts.2.2.2.2.2; omega)
            unfold RunBounded at growB
            rw [grown] at growB
            obtain ⟨gb1,_,_⟩ := growB
            dsimp only at gb1
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gTables gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,Or.inr ⟨fInv.transfer pm pa pb pc,kLe,vLe⟩,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb,Or.inr (by rw [capDouble,countOne]; omega),fun w below outside => by
                have := rInv.keysBelow; have := rInv.usedBelow; have := rInv.orderBelow; have := rInv.orderPosBelow
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (Or.inl ⟨by omega,by omega⟩),
                  gFrame w below (by omega),rFacts.1]⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finishD u capacity keys used values order orderPos bits rInv rTables rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,Or.inl ⟨fInv.transfer pm pa pb pc,rfl,rfl,rfl,rfl⟩,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb,
              Or.inl rfl,fun w _ outside => by
                have := rInv.keysBelow; have := rInv.valuesBelow; have := rInv.usedBelow; have := rInv.orderBelow
                have := rInv.orderPosBelow
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (by omega),rFacts.1]⟩

#print axioms htabSet_returned_desc_fine

/-- An actual table layout with its array block [lo, hi): an aligned table (block from the first of keys
and values to the end of order_pos, header separate), or a descending scratch table (block from
order_pos to the header end, header included). -/
def HtabLaid {F : Type} (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (lo hi : Nat) (state : PanSemStateFiniteExact 64 F) : Prop :=
  (HtabAligned keyLength table keys stride capacity used values order orderPos count bits state ∧
      lo = min keys.toNat values.toNat ∧ hi = orderPos.toNat + capacity.toNat * 8) ∨
    (HtabDescending keyLength table keys stride capacity used values order orderPos count bits state ∧
      lo = orderPos.toNat ∧ hi = table.toNat + 72)

theorem HtabLaid.code {F : Type} {keyLength table keys stride capacity used values order orderPos count : BitVec 64}
    {bits : Nat} {lo hi : Nat} {state : PanSemStateFiniteExact 64 F}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi state) :
    state.code = originalRuntimeCode := by
  rcases laid with ⟨inv,_,_⟩ | ⟨inv,_,_⟩
  · exact inv.code
  · exact inv.code

theorem HtabLaid.regions {F : Type} {keyLength table keys stride capacity used values order orderPos count : BitVec 64}
    {bits : Nat} {lo hi : Nat} {state : PanSemStateFiniteExact 64 F}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi state) :
    HtabRegions keyLength table keys stride capacity used values order orderPos count bits state := by
  rcases laid with ⟨inv,_,_⟩ | ⟨inv,_,_⟩
  · exact inv.toRegions
  · exact inv.toRegions

theorem HtabLaid.transfer {F G : Type} {keyLength table keys stride capacity used values order orderPos count : BitVec 64}
    {bits : Nat} {lo hi : Nat} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi s)
    (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code) :
    HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi r := by
  rcases laid with ⟨inv,l,h⟩ | ⟨inv,l,h⟩
  · exact Or.inl ⟨inv.transfer memory memaddrs be code,l,h⟩
  · exact Or.inr ⟨inv.transfer memory memaddrs be code,l,h⟩

/-- The discarded set call on an actual (aligned or descending) table: the post table is laid out with the
same block or a block at or above the heap pointer, memory below the heap pointer outside the header and the
old block is unchanged, and the capacity grows only past a quarter of the count. -/
theorem htabSet_call_normal_laid {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (lo hi : Nat)
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat) (lo' hi' : Nat),
      HtabLaid keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' lo' hi' post ∧
      OrderInv post capacity' count' used' order' orderPos' ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      ((lo' = lo ∧ hi' = hi) ∨ pointer.toNat ≤ lo')) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        (w.toNat < lo ∨ hi ≤ w.toNat) → post.memory w = state.memory w) := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_set")
    _ _ _ _ .one args (htabSet_installed state table key value laid.code) run
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  have entryT : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "t") =
      some (.val (.word table)) := by
    simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryK : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "key") =
      some (.val (.word key)) := by
    simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryV : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "value") =
      some (.val (.word value)) := by
    simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rcases laid with ⟨inv,rfl,rfl⟩ | ⟨inv,rfl,rfl⟩
  · obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables,capB,layout,outFrame⟩ := htabSet_returned_fine
      (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
        (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride capacity used values order orderPos count key value pointer bits
      (inv.transfer rfl rfl rfl rfl) entryT entryK entryV (by exact heap) pointerAligned headerBelow pointerInside
      (fun a h1 h2 h3 => by exact arena a h1 h2 h3) (tables.transfer rfl rfl rfl) room small
      (by change _ ≤ state.clock - 1; omega) bodyRun
    have postInv := outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
      (meta'.1.trans (inv.code.trans outInv.code.symm))
    refine ⟨⟨c',k',u',v',o',op',n',b',min k'.toNat v'.toNat,op'.toNat + c'.toNat * 8,Or.inl ⟨postInv,rfl,rfl⟩,
      outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm),shape,capB,?_⟩,
      locals,meta'.2.1,meta'.2.2.1,fun w below hdr outside => ?_⟩
    · rcases layout with ⟨rfl,rfl,rfl,rfl⟩ | ⟨kl,vl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (by omega)
    · rw [memory,outFrame w below hdr (by omega)]; rfl
  · obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables,capB,outFrame⟩ := htabSet_returned_desc_fine
      (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
        (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride capacity used values order orderPos count key value pointer bits
      (inv.transfer rfl rfl rfl rfl) entryT entryK entryV (by exact heap) pointerAligned headerBelow pointerInside
      (fun a h1 h2 h3 => by exact arena a h1 h2 h3) (tables.transfer rfl rfl rfl) room small
      (by change _ ≤ state.clock - 1; omega) bodyRun
    refine ⟨?_,locals,meta'.2.1,meta'.2.2.1,fun w below _ outside => by rw [memory,outFrame w below outside]; rfl⟩
    have postTables := outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    rcases outInv with ⟨d,rfl,rfl,rfl,rfl⟩ | ⟨a,kl,vl⟩
    · exact ⟨c',k',u',v',o',op',n',b',op'.toNat,table.toNat + 72,
        Or.inr ⟨d.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
          (meta'.1.trans (inv.code.trans d.code.symm)),rfl,rfl⟩,postTables,shape,capB,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨c',k',u',v',o',op',n',b',min k'.toNat v'.toNat,op'.toNat + c'.toNat * 8,
        Or.inl ⟨a.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
          (meta'.1.trans (inv.code.trans a.code.symm)),rfl,rfl⟩,postTables,shape,capB,Or.inr (by omega)⟩

#print axioms htabSet_call_normal_laid
end InitECandidate.Runtime
