import InitECandidate.Runtime.HtabHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ite_normal_cases_cond {F : Type} (s next : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (run : evaluateHOLFiniteState s (.ite condition yes no) = (none,next)) :
    (∃ w : BitVec 64, w ≠ 0 ∧ @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition =
        some (.val (.word w)) ∧ evaluateHOLFiniteState s yes = (none,next)) ∨
      (@evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word 0)) ∧
        evaluateHOLFiniteState s no = (none,next)) := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i w hw
    split at run
    · rename_i zero
      right
      have : w = 0 := by simpa using zero
      subst this
      exact ⟨hw,run⟩
    · rename_i nonzero
      exact Or.inl ⟨w,by simpa using nonzero,hw,run⟩
  · simp at run

/-- A word write outside the header cells and the occupancy array keeps the aligned table invariant. -/
theorem HtabAligned.write_outside {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (address value : BitVec 64)
    (header : ∀ k : Nat, k ≤ 64 → address ≠ table + BitVec.ofNat 64 k)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → address ≠ panByteAlignHOL (used + slot)) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits (sourceWriteWord s address value) := by
  have keep : ∀ k : Nat, k ≤ 64 → (sourceWriteWord s address value).memory (table + BitVec.ofNat 64 k) =
      s.memory (table + BitVec.ofNat 64 k) := by
    intro k hk; simp [sourceWriteWord,Ne.symm (header k hk)]
  have read : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead (sourceWriteWord s address value) used slot = hashOccupancyRead s used slot := by
    intro slot inside
    exact occupancyRead_congr_at _ s used slot (by simp [sourceWriteWord,Ne.symm (occupancy slot inside)]) rfl rfl
  exact {
    code := inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
    strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
    orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned, headerKeys := inv.headerKeys,
    headerValues := inv.headerValues, keysBefore := inv.keysBefore, valuesBefore := inv.valuesBefore,
    usedBefore := inv.usedBefore, orderBefore := inv.orderBefore, endBound := inv.endBound, fits := inv.fits,
    domain := fun a h1 h2 h3 => inv.domain a h1 h2 h3,
    cell0 := (keep 0 (by omega)).trans inv.cell0, cell8 := (keep 8 (by omega)).trans inv.cell8,
    cell16 := (keep 16 (by omega)).trans inv.cell16, cell24 := (keep 24 (by omega)).trans inv.cell24,
    cell32 := (keep 32 (by omega)).trans inv.cell32, cell40 := (keep 40 (by omega)).trans inv.cell40,
    cell48 := (keep 48 (by omega)).trans inv.cell48, cell56 := (keep 56 (by omega)).trans inv.cell56,
    cell64 := (keep 64 (by omega)).trans inv.cell64,
    agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot inside => (read slot inside).symm) }

#print axioms HtabAligned.write_outside

theorem htabSetGuard_shape : htabSetGuard = .cmp .lower (.load .one (.op .add [.var .local (ofString "t"),.const 16]))
    (.panop .mul [.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 24]),.const 1],.const 2]) := rfl

theorem eval_htabSetGuard {F : Type} (s : PanSemStateFiniteExact 64 F) (table capacity count : BitVec 64)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (d16 : s.memaddrs (table + 16#64)) (c16 : s.memory (table + 16#64) = .word capacity)
    (d24 : s.memaddrs (table + 24#64)) (c24 : s.memory (table + 24#64) = .word count)
    (small : count.toNat < 2 ^ 62) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) htabSetGuard =
      some (.val (.word (if capacity.toNat < (count.toNat + 1) * 2 then 1 else 0))) := by
  rw [htabSetGuard_shape]
  simp [evalHOLExact,evalListHOLExact,tL,memLoadHOLExact,isWfShapeExactHOL,d16,c16,d24,c24,wordOpHOL,wordOp,
    valueIsWord,valueWord,panOpHOL,Compiler.Encoders.Asm.wordCmpHOL]
  by_cases lt : capacity.toNat < (count.toNat + 1) * 2
  · simp [lt,BitVec.lt_def]; omega
  · simp [lt,BitVec.lt_def]; omega

#print axioms eval_htabSetGuard

/-- A returned existing-key update found the key at an in-range slot and wrote
only its value cell. -/
theorem htabSetUpdate_returned {F : Type} (r u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (table capacity values slot value : BitVec 64)
    (tL : r.locals.lookup (ofString "t") = some (.val (.word table)))
    (iL : r.locals.lookup (ofString "i") = some (.val (.word slot)))
    (valueL : r.locals.lookup (ofString "value") = some (.val (.word value)))
    (slotLe : slot.toNat ≤ capacity.toNat)
    (d16 : r.memaddrs (table + 16#64)) (c16 : r.memory (table + 16#64) = .word capacity)
    (d40 : r.memaddrs (table + 40#64)) (c40 : r.memory (table + 40#64) = .word values)
    (run : evaluateHOLFiniteState r htabSetUpdate = (some (.returned v),u)) :
    slot.toNat < capacity.toNat ∧ u.memory = (sourceWriteWord r (values + slot * 8) value).memory ∧
      u.memaddrs = r.memaddrs ∧ u.be = r.be ∧ u.code = r.code := by
  have shape : htabSetUpdate = .ite (.cmp .notEqual (.var .local (ofString "i"))
      (.load .one (.op .add [.var .local (ofString "t"),.const 16])))
      (.seq (.store (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 40]),
          .panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "value"))) (.return (.const 0))) .skip := rfl
  rw [shape,evaluateHOLFiniteState_ite] at run
  have cond : @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "i")) (.load .one (.op .add [.var .local (ofString "t"),.const 16]))) =
        some (.val (.word (if slot = capacity then 0 else 1))) := by
    simp [evalHOLExact,evalListHOLExact,iL,tL,memLoadHOLExact,isWfShapeExactHOL,d16,c16,wordOpHOL,wordOp,valueIsWord,
      valueWord,Compiler.Encoders.Asm.wordCmpHOL]
  rw [cond] at run
  by_cases same : slot = capacity
  · simp [same,evaluateHOLFiniteState_skip] at run
  · simp only [same,if_false,show (1 : BitVec 64) ≠ 0 by decide] at run
    have lt : slot.toNat < capacity.toNat := by
      have : slot.toNat ≠ capacity.toNat := fun h => same (BitVec.eq_of_toNat_eq h)
      omega
    have addr : @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a))
        (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 40]),.panop .mul [.var .local (ofString "i"),.const 8]]) =
          some (.val (.word (values + slot * 8))) := by
      simp [evalHOLExact,evalListHOLExact,iL,tL,memLoadHOLExact,isWfShapeExactHOL,d40,c40,wordOpHOL,wordOp,valueIsWord,
        valueWord,panOpHOL]
    have val : @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a))
        (.var .local (ofString "value")) = some (.val (.word value)) := by simp [evalHOLExact,valueL]
    have stored := store_seq_returned r u _ _ (values + slot * 8) value addr val run
    obtain ⟨m,a,b,c⟩ := return_const_state _ u 0 v stored
    exact ⟨lt,m,a,b,c⟩

#print axioms htabSetUpdate_returned

/-- A returned original set leaves an aligned table for the same key length and
stride: either the same capacity and count (existing key updated), or count + 1
with load at most one half (key inserted, after growth when needed). -/
theorem htabSet_returned_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned v),post)) :
    ∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
      refine ⟨capacity,keys,used,values,order,orderPos,count,bits,
        written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc),Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1)⟩
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
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be := by
        intro g capacity' keys' used' values' order' orderPos' bits' gInv gl roomG gClock gRun
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
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe⟩
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
            obtain ⟨⟨k',u',v',o',op',gInv⟩,gLocals,gAddr,gBe⟩ := htabGrow_call_normal_aligned u g _ keyLength table keys stride
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
            obtain ⟨fInv,fAddr,fBe⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1))⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe⟩ := finish u capacity keys used values order orderPos bits rInv rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1)⟩

#print axioms htabSet_returned_aligned

theorem htabSet_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (table key value : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htab_set") [.val (.word table),.val (.word key),.val (.word value)] =
      some (sourceFunctionBody Guest.guestFn_htab_set,
        ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update
          (ofString "value",.val (.word value)),.one) :=
  pan_three_word_lookup state.code.lookup (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_htab_set) table key value (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_hashSet_lookup)

/-- A handler-free `htab_set` call on word arguments costs setBodyCost + 1 in every outcome. -/
theorem runBounded_htabSet_call {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])
      (setBodyCost keyLength capacity count + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabSet_installed state table key value inv.code] at lookup
  cases lookup
  exact evaluate_htabSet_body_bounded _ keyLength table keys stride capacity used values order orderPos count key value
    pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega)

/-- After a normally finishing discarded `htab_set` call, the table is aligned
for the same key length and stride, with the same count and capacity or with
count + 1 at load at most one half; caller locals, address map and endianness
are unchanged. -/
theorem htabSet_call_normal_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat))) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_set")
    _ _ _ _ .one args (htabSet_installed state table key value inv.code) run
  obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe⟩ := htabSet_returned_aligned
    (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride
    capacity used values order orderPos count key value pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  exact ⟨⟨c',k',u',v',o',op',n',b',outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    (meta'.1.trans (inv.code.trans outInv.code.symm)),shape⟩,locals,meta'.2.1,meta'.2.2.1⟩

/-- Discarded `htab_set` calls keep non-heap globals and an aligned in-arena heap word moves only upward. -/
theorem htabSet_call_normalRel (arguments : List (ExpHOL 64)) :
    NormalRel HeapRel (.call (some (none,none)) (ofString "htab_set") arguments) :=
  normalRel_discard_call heapRel_preorder _ _ _ _ _ originalRuntimeCode_hashSet_lookup (NormalRel.returned htabSet_normalRel)

#print axioms runBounded_htabSet_call
#print axioms htabSet_call_normal_aligned
#print axioms htabSet_call_normalRel
end InitECandidate.Runtime
