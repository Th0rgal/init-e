import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.AllocationFailureTail
import InitECandidate.Runtime.TrapCallTerminal
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.HashGrowRehashSyntax
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original allocator body had a safe request and finish, returned
the old heap pointer and changed only the heap-pointer global. -/
theorem alloc_body_returned {F : Type} (state post : PanSemStateFiniteExact 64 F) (pointer size : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size))) (w : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc) = (some (.returned w),post)) :
    size ≤ (33806089496 : BitVec 64) - pointer ∧ (allocationEnd pointer size).toNat ≤ 33806089496 ∧
      w = .val (.word pointer) ∧ post.memory = state.memory ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.code = state.code ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd pointer size))) state).globals := by
  have trapArgs : ∀ {G : Type} (s : PanSemStateFiniteExact 64 G), evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) [.const 1] = some [.val (.word (1 : BitVec 64))] := by
    intro G s; simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
  · by_cases finish : (allocationEnd pointer size).toNat ≤ 33806089496
    · obtain ⟨p',run',_,_,memory,postCode,addresses,_,endian,globals⟩ :=
        evaluate_source_alloc_success state pointer size heapGlobal sizeLocal request finish
      rw [run'] at run
      obtain ⟨e,rfl⟩ := Prod.mk.inj run
      simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
      exact ⟨request,finish,e.symm,memory,addresses,endian,postCode,globals⟩
    · exfalso
      rw [source_alloc_body] at run
      obtain ⟨pv,i1,e1,r1,_,_,_,_⟩ := dec_returned_state run
      have pEval : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word pointer)) := by
        simp [evalHOLExact,heapGlobal]
      rw [pEval] at e1
      cases e1
      generalize hp : setVarHOLFinite (ofString "p") (.val (.word pointer)) state = sp at r1
      have pL : sp.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
        rw [← hp]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have nL : sp.locals.lookup (ofString "n") = some (.val (.word size)) := by
        rw [← hp]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,sizeLocal]
      unfold allocationAfterPointer at r1
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,
        eval_allocationRequestCheck sp pointer size pL nL request] at r1
      simp only [if_false,if_true,evaluateHOLFiniteState_skip] at r1
      obtain ⟨qv,i2,e2,r2,_,_,_,_⟩ := dec_returned_state r1
      rw [eval_allocationEndExpression sp pointer size pL nL] at e2
      cases e2
      generalize hq : setVarHOLFinite (ofString "q") (.val (.word (allocationEnd pointer size))) sp = sq at r2
      have qL : sq.locals.lookup (ofString "q") = some (.val (.word (allocationEnd pointer size))) := by
        rw [← hq]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have sqCode : sq.code = originalRuntimeCode := by rw [← hq,← hp]; exact code
      have guard : @evalHOLExact 64 F _ sq.toExact (fun a => Classical.propDecidable (sq.memaddrs a))
          (.cmp .lower (.const 33806089496) (.var .local (ofString "q"))) = some (.val (.word 1)) := by
        have over : 33806089496 < (allocationEnd pointer size).toNat := by omega
        simp [evalHOLExact,qL,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,over]
      unfold allocationFinish at r2
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at r2
      simp only [ne_eq,show (1 : BitVec 64) ≠ 0 by decide,not_false_eq_true,if_true] at r2
      cases trap : evaluateHOLFiniteState sq (.call (some (none,none)) (ofString "trap_with") [.const 1]) with
      | mk tr tp =>
        rw [trap] at r2
        have notNone := evaluate_trap_call_terminal sq (.const 1) 1 sqCode (trapArgs sq)
        have notRet := discard_call_not_returned sq (ofString "trap_with") [.const 1] w
        rw [trap] at notNone notRet
        cases tr with
        | none => exact notNone rfl
        | some r =>
          obtain ⟨er,_⟩ := Prod.mk.inj r2
          exact notRet er
  · exfalso
    rw [source_alloc_body] at run
    obtain ⟨pv,i1,e1,r1,_,_,_,_⟩ := dec_returned_state run
    have pEval : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.var .global (ofString "heap_ptr")) = some (.val (.word pointer)) := by
      simp [evalHOLExact,heapGlobal]
    rw [pEval] at e1
    cases e1
    generalize hp : setVarHOLFinite (ofString "p") (.val (.word pointer)) state = sp at r1
    have pL : sp.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      rw [← hp]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have nL : sp.locals.lookup (ofString "n") = some (.val (.word size)) := by
      rw [← hp]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,sizeLocal]
    have spCode : sp.code = originalRuntimeCode := by rw [← hp]; exact code
    have failure := (evaluate_allocationAfterPointer_failure sp pointer size spCode pL nL
      (by have := mt BitVec.le_def.mpr request; omega)).1
    rw [failure] at r1
    exact discard_call_not_returned sp _ _ w (congrArg Prod.fst r1)

#print axioms alloc_body_returned

theorem HtabAligned.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (memory : r.memory = s.memory) (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) (code : r.code = s.code) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits r := by
  have read : ∀ slot, hashOccupancyRead r used slot = hashOccupancyRead s used slot := by
    intro slot; unfold hashOccupancyRead; rw [memory,addresses,endian]
  exact {
    code := code.trans inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
    strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
    orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned, headerKeys := inv.headerKeys,
    headerValues := inv.headerValues, keysBefore := inv.keysBefore, valuesBefore := inv.valuesBefore,
    usedBefore := inv.usedBefore, orderBefore := inv.orderBefore, endBound := inv.endBound, fits := inv.fits,
    domain := fun a h1 h2 h3 => by rw [addresses]; exact inv.domain a h1 h2 h3,
    cell0 := by rw [memory]; exact inv.cell0, cell8 := by rw [memory]; exact inv.cell8,
    cell16 := by rw [memory]; exact inv.cell16, cell24 := by rw [memory]; exact inv.cell24,
    cell32 := by rw [memory]; exact inv.cell32, cell40 := by rw [memory]; exact inv.cell40,
    cell48 := by rw [memory]; exact inv.cell48, cell56 := by rw [memory]; exact inv.cell56,
    cell64 := by rw [memory]; exact inv.cell64,
    agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot _ => (read slot).symm) }

/-- A normally finishing discarded insertion call into an aligned table with a
free slot leaves the aligned invariant at count + 1 and the caller's locals. -/
theorem htabInsertRaw_call_normal_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    HtabAligned keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) →
        post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htab_insert_raw") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],
        sourceFunctionBody Guest.guestFn_htab_insert_raw,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashInsert_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_insert_raw") (ofString "t") (ofString "key")
    (ofString "value") (sourceFunctionBody Guest.guestFn_htab_insert_raw) table key value
    (by decide) (by decide) (by decide) installed
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_insert_raw")
    _ _ _ _ .one args lookup run
  generalize hentry : callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update
      (ofString "value",.val (.word value))) = entry at bodyRun
  have entryInv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits entry :=
    inv.transfer (by rw [← hentry]; rfl) (by rw [← hentry]; rfl) (by rw [← hentry]; rfl) (by rw [← hentry]; rfl)
  obtain ⟨outInv,outAddr,outBe,outFrame⟩ := htabInsertRaw_returned_aligned entry output v table key value keyLength keys
    stride capacity used values order orderPos count bits entryInv
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    room small (by rw [← hentry]; change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_insert_raw")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  have entryAddr : entry.memaddrs = state.memaddrs := by rw [← hentry]; rfl
  have entryBe : entry.be = state.be := by rw [← hentry]; rfl
  have entryMem : entry.memory = state.memory := by rw [← hentry]; rfl
  refine ⟨outInv.transfer memory (meta'.2.1.trans (outAddr.trans entryAddr).symm)
      (meta'.2.2.1.trans (outBe.trans entryBe).symm) (meta'.1.trans (inv.code.trans outInv.code.symm)),
    locals,meta'.2.1,meta'.2.2.1,fun watched outside => ?_⟩
  rw [memory,outFrame watched outside,entryMem]

#print axioms htabInsertRaw_call_normal_aligned

/-- A normally finishing declaration: the initializer evaluated, the body
finished normally from the bound state, and only the declared local is restored. -/
theorem dec_normal_state {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (none,post)) :
    ∃ value inner, @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
        initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (none,inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      post.clock = inner.clock ∧
      (∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) ∧
      post.locals.lookup name = s.locals.lookup name := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run
  · rename_i value evaluated
    split at run
    · cases inner : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r i =>
        rw [inner] at run
        obtain ⟨e,p⟩ := Prod.mk.inj run
        simp only at e
        subst p
        refine ⟨value,i,evaluated,by rw [inner,e],rfl,rfl,rfl,rfl,rfl,fun k ne => ?_,?_⟩
        · rw [resVarEq_lookup,if_neg ne]
        · simp [resVarEq_lookup]
    · simp at run

theorem call_args_none {F : Type} (state : PanSemStateFiniteExact 64 F) (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = none) :
    evaluateHOLFiniteState state (.call info function arguments) = (some .error,state) := by
  rw [evaluateHOLFiniteState_call,args]

theorem evaluate_increment_local {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (value : BitVec 64)
    (binding : state.locals.lookup name = some (.val (.word value))) :
    evaluateHOLFiniteState state (.assign .local name (.op .add [.var .local name,.const 1])) =
      (none,setVarHOLFinite name (.val (.word (value + 1))) state) := by
  simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,
    valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]

#print axioms dec_normal_state

theorem rehash_args_cases {F : Type} (s : PanSemStateFiniteExact 64 F) (table ko so vo : BitVec 64) (iv : ValueHOL 64)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysL : s.locals.lookup (ofString "keys") = some (.val (.word ko)))
    (strideL : s.locals.lookup (ofString "stride") = some (.val (.word so)))
    (valsL : s.locals.lookup (ofString "vals") = some (.val (.word vo)))
    (iL : s.locals.lookup (ofString "i") = some iv) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"),
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .load .one (hashOrderAddress (ofString "vals") (ofString "i"))] = none ∨
    ∃ a y : BitVec 64, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"),
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .load .one (hashOrderAddress (ofString "vals") (ofString "i"))] =
        some [.val (.word table),.val (.word a),.val (.word y)] := by
  rw [evalListHOLFinite_eq_toExact]
  cases iv with
  | val w =>
    cases w with
    | word x =>
      simp [evalListHOLExact,evalHOLExact,tL,keysL,strideL,valsL,iL,hashOrderAddress,panOpHOL,wordOpHOL,wordOp,
        valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
      by_cases d : s.memaddrs (vo + x * 8#64)
      · right
        obtain ⟨y,hy⟩ : ∃ y, s.memory (vo + x * 8#64) = .word y := by
          cases h : s.memory (vo + x * 8#64) with
          | word y => exact ⟨y,rfl⟩
        refine ⟨ko + x * so,y,?_⟩
        rw [if_pos d,hy]
      · left
        rw [if_neg d]
  | _ =>
    left
    simp [evalListHOLExact,evalHOLExact,tL,keysL,strideL,valsL,iL,hashOrderAddress,panOpHOL,wordOpHOL,wordOp,
      valueIsWord,valueWord]

theorem HtabAligned.header_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (k : Nat) (hk : k ≤ 64) (ha : k % 8 = 0) : s.memaddrs (table + BitVec.ofNat 64 k) := by
  have fits : table.toNat + k < 2 ^ 64 := by have := inv.headerKeys; have := keys.isLt; omega
  have eq := word_add_toNat table k fits
  have := inv.tableAligned
  have := inv.headerKeys
  have := inv.keysBefore
  have := inv.usedBefore
  have := inv.orderBefore
  exact inv.domain _ (by rw [eq]; omega) (by rw [eq]; omega) (by rw [eq]; omega)

/-- Cost of one handler-free insertion call into a table of the given capacity. -/
def insertCallCost (keyLength capacity : BitVec 64) : Nat :=
  keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1

/-- Rehash-loop rank: counter k ≤ nitems with at most `n` items left, the old
arrays and table locals are words, and the fresh table is aligned at count k. -/
def GrowRehashRank (keyLength table keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ K : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word K)) ∧ K.toNat ≤ items.toNat ∧
    items.toNat - K.toNat ≤ n ∧
    s.locals.lookup (ofString "nitems") = some (.val (.word items)) ∧
    s.locals.lookup (ofString "t") = some (.val (.word table)) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "keys") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "stride") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "vals") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "order") = some (.val (.word w))) ∧
    HtabAligned keyLength table keys stride capacity used values order orderPos K bits s

/-- The actual growth rehash loop, from rank n, spends at most
n * (insertCallCost + 1) ticks in every outcome; each normal iteration inserts
one item into the fresh aligned table. -/
theorem growRehashLoop_run (keyLength table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (fitsIn : items.toNat < capacity.toNat) (capSmall : capacity.toNat < 2 ^ 62)
    (small : keyLength.toNat ≤ 33806089496) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      GrowRehashRank keyLength table keys stride capacity used values order orderPos items bits state n →
      n * (insertCallCost keyLength capacity + 1) ≤ state.clock →
      RankedOutcome state (.cmp .less (.var .local (ofString "k")) (.var .local (ofString "nitems")))
        (n * (insertCallCost keyLength capacity + 1))
        (GrowRehashRank keyLength table keys stride capacity used values order orderPos items bits) False
        (evaluateHOLFiniteState state hashGrowRehashLoop) := by
  refine rankedWhile_run _ hashGrowRehashBody (insertCallCost keyLength capacity)
    (GrowRehashRank keyLength table keys stride capacity used values order orderPos items bits) False ?_ ?_
  · intro F s ranked v hv
    obtain ⟨K,kL,_,left,nL,_⟩ := ranked
    rw [eval_localBound_less s (ofString "k") (ofString "nitems") .less (Or.inl rfl) K items (by omega) (by omega) kL nL] at hv
    have : ¬ K.toNat < items.toNat := by omega
    simp [this] at hv
    exact hv.symm
  · intro F s n v code' ranked hv nonzero budget'
    obtain ⟨K,kL,kLe,left,nL,tL,⟨ko,keysL⟩,⟨so,strideL⟩,⟨vo,valsL⟩,⟨oo,orderL⟩,inv⟩ := ranked
    rw [eval_localBound_less s (ofString "k") (ofString "nitems") .less (Or.inl rfl) K items (by omega) (by omega) kL nL] at hv
    have lt : K.toNat < items.toNat := by
      by_cases h : K.toNat < items.toNat
      · exact h
      · simp [h] at hv; exact absurd hv.symm nonzero
    have room : K.toNat < capacity.toNat := by omega
    have dInv : HtabAligned keyLength table keys stride capacity used values order orderPos K bits (decClockHOLFinite s) :=
      inv.transfer rfl rfl rfl rfl
    obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead (decClockHOLFinite s) used)
      (by rw [← dInv.agreement]; exact room)
    -- per-entry facts used by both the bound and the rank
    have entryFacts : ∀ iv : ValueHOL 64,
        let e := setVarHOLFinite (ofString "i") iv (decClockHOLFinite s)
        HtabAligned keyLength table keys stride capacity used values order orderPos K bits e ∧
        e.locals.lookup (ofString "t") = some (.val (.word table)) ∧
        e.locals.lookup (ofString "keys") = some (.val (.word ko)) ∧
        e.locals.lookup (ofString "stride") = some (.val (.word so)) ∧
        e.locals.lookup (ofString "vals") = some (.val (.word vo)) ∧
        e.locals.lookup (ofString "i") = some iv ∧
        e.locals.lookup (ofString "k") = some (.val (.word K)) ∧ e.clock = s.clock - 1 := by
      intro iv
      refine ⟨dInv.transfer rfl rfl rfl rfl,?_,?_,?_,?_,?_,?_,rfl⟩ <;>
        simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,decClockHOLFinite,
          tL,keysL,strideL,valsL,kL]
    have bounded : RunBounded (decClockHOLFinite s) hashGrowRehashBody (insertCallCost keyLength capacity) := by
      unfold hashGrowRehashBody
      apply RunBounded.dec
      intro iv _
      obtain ⟨eInv,eT,eKeys,eStride,eVals,eI,_,eClock⟩ := entryFacts iv
      rw [show insertCallCost keyLength capacity = insertCallCost keyLength capacity + 0 from rfl]
      refine RunBounded.seq ?_ (by rw [eClock]; unfold insertCallCost at budget' ⊢; omega) ?_
      · rcases rehash_args_cases _ table ko so vo iv eT eKeys eStride eVals eI with none | ⟨a,y,args⟩
        · unfold RunBounded
          rw [call_args_none _ _ _ _ none]
          exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩
        · exact runBounded_htabInsertRaw_call _ none _ _ _ table a y capacity keyLength stride keys used empty bits
            eInv.code args (eInv.header_domain 16 (by omega) (by omega)) eInv.cell16
            (eInv.header_domain 0 (by omega) (by omega)) eInv.cell0
            (eInv.header_domain 8 (by omega) (by omega)) eInv.cell8
            (eInv.header_domain 32 (by omega) (by omega)) eInv.cell32
            (eInv.header_domain 48 (by omega) (by omega)) eInv.cell48
            eInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
            (by rw [eClock]; unfold insertCallCost at budget'; omega)
      · intro next _ nextCode _
        exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans eInv.code) (Nat.zero_le _)
    obtain ⟨b1,b2,b3⟩ := bounded
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases hrun : evaluateHOLFiniteState (decClockHOLFinite s) hashGrowRehashBody with
        | mk r post =>
          rw [hrun] at normal
          simp only at normal
          subst normal
          dsimp only
          unfold hashGrowRehashBody at hrun
          obtain ⟨iv,inner,_,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state hrun
          obtain ⟨eInv,eT,eKeys,eStride,eVals,eI,eK,eClock⟩ := entryFacts iv
          rw [evaluateHOLFiniteState_seq_line780] at innerRun
          cases callRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") iv (decClockHOLFinite s))
              (.call (some (none,none)) (ofString "htab_insert_raw")
                [.var .local (ofString "t"),
                 .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
                 .load .one (hashOrderAddress (ofString "vals") (ofString "i"))]) with
          | mk cr mid =>
            rw [callRun] at innerRun
            cases cr with
            | some r => simp at innerRun
            | none =>
              simp only at innerRun
              rcases rehash_args_cases _ table ko so vo iv eT eKeys eStride eVals eI with none | ⟨a,y,args⟩
              · rw [call_args_none _ _ _ _ none] at callRun
                simp at callRun
              · obtain ⟨midInv,midLocals,midAddr,midBe,_⟩ := htabInsertRaw_call_normal_aligned _ mid _ _ _ table a y
                  keyLength keys stride capacity used values order orderPos K bits eInv args room small
                  (by rw [eClock]; unfold insertCallCost at budget'; omega) callRun
                have kMid : mid.locals.lookup (ofString "k") = some (.val (.word K)) := by rw [midLocals]; exact eK
                rw [evaluate_increment_local mid (ofString "k") K kMid] at innerRun
                obtain ⟨_,rfl⟩ := Prod.mk.inj innerRun
                have keep : ∀ x, x ≠ ofString "k" → x ≠ ofString "i" → post.locals.lookup x = s.locals.lookup x := by
                  intro x nk ni
                  rw [plocals x ni]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nk]
                  rw [midLocals]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
                  rfl
                have noWrapK : (K + 1).toNat = K.toNat + 1 := by
                  rw [BitVec.toNat_add_of_lt (by have := items.isLt; simp; omega)]; rfl
                refine ⟨n,le_refl _,⟨K + 1,?_,by rw [noWrapK]; omega,by rw [noWrapK]; omega,
                  by rw [keep _ (by decide) (by decide)]; exact nL,
                  by rw [keep _ (by decide) (by decide)]; exact tL,
                  ⟨ko,by rw [keep _ (by decide) (by decide)]; exact keysL⟩,
                  ⟨so,by rw [keep _ (by decide) (by decide)]; exact strideL⟩,
                  ⟨vo,by rw [keep _ (by decide) (by decide)]; exact valsL⟩,
                  ⟨oo,by rw [keep _ (by decide) (by decide)]; exact orderL⟩,
                  midInv.transfer (pm.trans rfl) (pa.trans rfl) (pb.trans rfl) (pc.trans rfl)⟩,?_⟩
                · rw [plocals _ (by decide)]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
                · rw [pc]
                  change mid.code = s.code
                  rw [midInv.code,code']
      · exact absurd cont (by
          have := evaluate_noTopContinue hashGrowRehashBody (by decide) (decClockHOLFinite s); exact this)
    · intro brk
      exact absurd brk (by
        have := evaluate_noTopBreak hashGrowRehashBody (by decide) (decClockHOLFinite s); exact this)
#print axioms growRehashLoop_run
end InitECandidate.Runtime
