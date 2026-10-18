import InitECandidate.Runtime.HtabInsertRawBound
import InitECandidate.Runtime.HtabFindSlotReturned
import InitECandidate.Runtime.HashInsertTailMemory
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.HashOccupancyPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned declared call, exposing the callee's returned run and a resumed
state that carries the callee's final memory with the caller's other locals. -/
theorem decCall_returned_body {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (some (.returned v),post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (returnShape : ShapeHOL) (w : ValueHOL 64) (bodyPost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w),bodyPost) ∧
      resumed.memory = bodyPost.memory ∧ resumed.memaddrs = bodyPost.memaddrs ∧ resumed.be = bodyPost.be ∧
      resumed.code = bodyPost.code ∧
      (bodyPost.clock ≤ (callEntryStateHOLFinite s callee).clock → resumed.clock = bodyPost.clock) ∧
      resumed.locals.lookup name = some w ∧
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧
      evaluateHOLFiniteState resumed continuation = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r bodyPost =>
          rw [bodyRun] at run
          dsimp only [fixClockHOLFinite] at run
          rcases r with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; done)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨values,body,callee,returnShape,w,bodyPost,_,_,rfl,lookup,bodyRun,?m,?a,?b,?c,?k,?n,?l,Prod.ext e rfl,
              ?pm,?pa,?pb,?pc⟩
            case m => rfl
            case a => rfl
            case b => rfl
            case c => rfl
            case pm => rw [← p]
            case pa => rw [← p]
            case pb => rw [← p]
            case pc => rw [← p]
            case k =>
              intro le
              change (if _ then _ else _) = _
              rw [if_neg (by omega)]
            case n => simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            case l =>
              intro k ne
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
          · simp at run

/-- Partial correctness of a normal loop exit: an invariant kept by the loop
tick and by normal and `continue` iterations holds at a normal exit, where the
condition evaluated to zero, provided the body never breaks. -/
theorem while_normal_exit (condition : ExpHOL 64) (body : ProgHOL 64)
    (Inv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (clockFree : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Inv s → Inv (decClockHOLFinite s))
    (keeps : ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F), Inv s →
      (evaluateHOLFiniteState s body = (none,post) ∨ evaluateHOLFiniteState s body = (some .continue,post)) → Inv post)
    (noBreak : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s body).1 ≠ some .break) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.clock = n → Inv state →
      ∀ post, evaluateHOLFiniteState state (.while condition body) = (none,post) →
        Inv post ∧ evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) condition =
          some (.val (.word 0)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state clock invariant post run
    rw [evaluateHOLFiniteState_while_total] at run
    split at run
    · rename_i w hw
      split at run
      · split at run
        · simp at run
        · dsimp only at run
          rw [fixClockHOLFinite_evaluateState] at run
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have broke := noBreak (decClockHOLFinite state)
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk r mid =>
            rw [bodyRun] at run remaining broke
            have smaller : mid.clock < n := by
              change mid.clock ≤ state.clock - 1 at remaining
              omega
            cases r with
            | none =>
              exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inl bodyRun)) post run
            | some r =>
              cases r with
              | «continue» =>
                exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inr bodyRun)) post run
              | «break» => exact absurd rfl broke
              | _ => simp at run
      · rename_i zero
        simp only [Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        refine ⟨invariant,?_⟩
        rw [hw]
        simp only [ne_eq,Decidable.not_not] at zero
        rw [zero]
    · simp at run

/-- A discarding handler-free call never reports a returned value. -/
theorem discard_call_not_returned {F : Type} (state : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  repeat' first | split | (simp; done) | simp_all

/-- A zero probe condition reads an actual zero occupancy byte. -/
theorem hashProbeOccupied_zero_read {F : Type} (state : PanSemStateFiniteExact 64 F) (index used : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (zero : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (hashProbeOccupied (ofString "i")) = some (.val (.word 0))) :
    hashOccupancyRead state used index = some 0 := by
  unfold hashOccupancyRead
  rw [evalHOLFinite_eq_toExact] at zero
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) with
  | none =>
    simp [hashProbeOccupied,evalHOLExact,evalListHOLExact,indexLocal,usedLocal,wordOpHOL,wordOp,valueIsWord,
      valueWord,loaded] at zero
  | some byte =>
    rw [eval_hashProbeOccupied state _ index used byte indexLocal usedLocal loaded] at zero
    by_cases b : byte = 0
    · rw [b]
    · exfalso
      have : (BitVec.ofNat 64 byte.toNat) ≠ 0 := by
        intro h
        apply b
        have h2 : byte.toNat = 0 := by
          have := congrArg BitVec.toNat h
          have small : byte.toNat < 2 ^ 64 := by have := byte.toNat_lt; omega
          simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using this
        exact UInt8.toNat_inj.mp h2
      have hb : (BitVec.ofNat 64 byte.toNat == 0) = false := by rw [beq_eq_false_iff_ne]; exact this
      simp only [Compiler.Encoders.Asm.wordCmpHOL,hb,Bool.not_false,if_true] at zero
      simp at zero

#print axioms decCall_returned_body
#print axioms while_normal_exit
#print axioms discard_call_not_returned
#print axioms hashProbeOccupied_zero_read

theorem hashProbeStep_not_break {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) :
    (evaluateHOLFiniteState state (hashProbeStep name)).1 ≠ some .break := by
  unfold hashProbeStep
  rw [evaluateHOLFiniteState_assign]
  split <;> (try split) <;> simp

theorem occupancyRead_congr_at {F G : Type} (r : PanSemStateFiniteExact 64 F) (q : PanSemStateFiniteExact 64 G)
    (used slot : BitVec 64)
    (memory : r.memory (panByteAlignHOL (used + slot)) = q.memory (panByteAlignHOL (used + slot)))
    (addresses : r.memaddrs = q.memaddrs) (endian : r.be = q.be) :
    hashOccupancyRead r used slot = hashOccupancyRead q used slot := by
  unfold hashOccupancyRead panMemLoadByteHOL
  generalize panByteAlignHOL (used + slot) = a at memory ⊢
  show (match r.memory a with
      | HolWordLab.word value => @ite _ (r.memaddrs a) (Classical.propDecidable _)
          (some (panGetByteHOL (used + slot) value r.be)) none) =
    (match q.memory a with
      | HolWordLab.word value => @ite _ (q.memaddrs a) (Classical.propDecidable _)
          (some (panGetByteHOL (used + slot) value q.be)) none)
  rw [memory,endian]
  cases q.memory a with
  | word value => rw [addresses]

theorem word_ne_of_toNat {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (congrArg BitVec.toNat e)

theorem htabInsertRawFinish_eq : htabInsertRawFinish = hashInsertValueTail := rfl

/-- A table whose header and arrays satisfy the source layout, with an
aligned-cell address domain over the table span (the canonical arena shape),
and whose count agrees with the occupied slots. -/
structure HtabAligned {F : Type}
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  power : capacity.toNat = 2 ^ bits
  tableAligned : table.toNat % 8 = 0
  keysAligned : keys.toNat % 8 = 0
  strideAligned : stride.toNat % 8 = 0
  valuesAligned : values.toNat % 8 = 0
  usedAligned : used.toNat % 8 = 0
  orderAligned : order.toNat % 8 = 0
  orderPosAligned : orderPos.toNat % 8 = 0
  headerKeys : table.toNat + 72 ≤ keys.toNat
  headerValues : table.toNat + 72 ≤ values.toNat
  keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat
  valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat
  usedBefore : used.toNat + capacity.toNat ≤ order.toNat
  orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat
  endBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496
  fits : keyLength.toNat ≤ stride.toNat
  domain : ∀ address : BitVec 64, address.toNat % 8 = 0 → table.toNat ≤ address.toNat →
    address.toNat < orderPos.toNat + capacity.toNat * 8 → state.memaddrs address
  cell0 : state.memory (table + 0) = .word keyLength
  cell8 : state.memory (table + 8) = .word stride
  cell16 : state.memory (table + 16) = .word capacity
  cell24 : state.memory (table + 24) = .word count
  cell32 : state.memory (table + 32) = .word keys
  cell40 : state.memory (table + 40) = .word values
  cell48 : state.memory (table + 48) = .word used
  cell56 : state.memory (table + 56) = .word order
  cell64 : state.memory (table + 64) = .word orderPos
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)

theorem eval_header_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : MlS) (pointer offset value : BitVec 64)
    (binding : state.locals.lookup base = some (.val (.word pointer)))
    (domain : state.memaddrs (pointer + offset)) (cell : state.memory (pointer + offset) = .word value) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress base offset)) = some (.val (.word value)) := by
  simp only [evalHOLExact,isWfShapeExactHOL]
  rw [eval_hashLocalAddress state base pointer offset binding]
  simp [memLoadHOLExact,domain,cell]

/-- A returned declaration: the initializer evaluated, the body returned from
the bound state, and memory/addresses/endianness/code are the body's. -/
theorem dec_returned_state {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (some (.returned v),post)) :
    ∃ value inner, @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
        initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
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
        exact ⟨value,i,evaluated,by rw [inner,e],rfl,rfl,rfl,rfl⟩
    · simp at run

/-- The insertion's table and argument locals. -/
def InsertLocals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table key value capacity keyLength stride keys used order orderPos : BitVec 64) : Prop :=
  s.locals.lookup (ofString "t") = some (.val (.word table)) ∧
  s.locals.lookup (ofString "key") = some (.val (.word key)) ∧
  s.locals.lookup (ofString "value") = some (.val (.word value)) ∧
  s.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
  s.locals.lookup (ofString "klen") = some (.val (.word keyLength)) ∧
  s.locals.lookup (ofString "stride") = some (.val (.word stride)) ∧
  s.locals.lookup (ofString "keys") = some (.val (.word keys)) ∧
  s.locals.lookup (ofString "used") = some (.val (.word used)) ∧
  s.locals.lookup (ofString "order") = some (.val (.word order)) ∧
  s.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))

def insertLocalNames : List MlS :=
  [ofString "t",ofString "key",ofString "value",ofString "cap",ofString "klen",ofString "stride",
    ofString "keys",ofString "used",ofString "order",ofString "order_pos"]

theorem InsertLocals.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {table key value capacity keyLength stride keys used order orderPos : BitVec 64}
    (facts : InsertLocals s table key value capacity keyLength stride keys used order orderPos)
    (same : ∀ k ∈ insertLocalNames, r.locals.lookup k = s.locals.lookup k) :
    InsertLocals r table key value capacity keyLength stride keys used order orderPos := by
  obtain ⟨a,b,c,d,e,f,g,h,i,j⟩ := facts
  simp only [insertLocalNames,List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp,forall_eq] at same
  obtain ⟨a',b',c',d',e',f',g',h',i',j'⟩ := same
  exact ⟨a'.trans a,b'.trans b,c'.trans c,d'.trans d,e'.trans e,f'.trans f,g'.trans g,h'.trans h,i'.trans i,j'.trans j⟩

theorem InsertLocals.setVar {F : Type} {s : PanSemStateFiniteExact 64 F}
    {table key value capacity keyLength stride keys used order orderPos : BitVec 64}
    (facts : InsertLocals s table key value capacity keyLength stride keys used order orderPos)
    (name : MlS) (x : ValueHOL 64) (fresh : name ∉ insertLocalNames) :
    InsertLocals (setVarHOLFinite name x s) table key value capacity keyLength stride keys used order orderPos := by
  apply facts.transfer
  intro k member
  have : k ≠ name := fun e => fresh (e ▸ member)
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm this]

#print axioms InsertLocals.setVar

theorem eval_hashFind_comparison_args_exact {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index keys stride key keyLength : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word (keys + index * stride)),.val (.word key),.val (.word keyLength)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [hashFindComparisonAddress,evalListHOLExact,evalHOLExact,indexLocal,keysLocal,strideLocal,keyLocal,
    lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

theorem word_add_toNat (a : BitVec 64) (k : Nat) (fits : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  have hk : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [hk]; omega),hk]

theorem word_mul_add_toNat (a i c : BitVec 64) (fits : a.toNat + i.toNat * c.toNat < 2 ^ 64) :
    (a + i * c).toNat = a.toNat + i.toNat * c.toNat := by
  have mul : (i * c).toNat = i.toNat * c.toNat := BitVec.toNat_mul_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [mul]; omega),mul]

theorem byteAlign_toNat (a : BitVec 64) : (panByteAlignHOL a).toNat = a.toNat / 8 * 8 := by
  unfold panByteAlignHOL
  simp only [show (64 / 8 : Nat).log2 = 3 by decide]
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := a.isLt
  omega

#print axioms byteAlign_toNat

/-- A returned original insertion into an aligned table with a free slot keeps
the aligned table invariant with count + 1, keeps addresses/endianness and
changes no memory outside the table span. -/
theorem htabInsertRaw_returned_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_insert_raw) = (some (.returned v),post)) :
    HtabAligned keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) →
        post.memory watched = state.memory watched := by
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have tableFits : table.toNat + 72 < 2 ^ 64 := by have := inv.headerKeys; have := keys.isLt; omega
  have header : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk => word_add_toNat table k (by omega)
  have headerDomain : ∀ k : Nat, k ≤ 64 → k % 8 = 0 → state.memaddrs (table + BitVec.ofNat 64 k) := by
    intro k hk ha
    apply inv.domain
    · rw [header k hk]; have := inv.tableAligned; omega
    · rw [header k hk]; omega
    · rw [header k hk]; have := inv.headerKeys; have := inv.usedBefore; have := inv.keysBefore; have := inv.orderBefore; omega
  rw [source_htabInsertRaw_body] at run
  obtain ⟨v1,i1,e1,r1,m1,a1,b1,c1⟩ := dec_returned_state run
  rw [eval_header_load state _ table 16 capacity tableLocal (by exact headerDomain 16 (by omega) (by omega)) (by exact inv.cell16)] at e1
  cases e1
  have t1 : (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state).locals.lookup (ofString "t") =
      some (.val (.word table)) := by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal]
  obtain ⟨v2,i2,e2,r2,m2,a2,b2,c2⟩ := dec_returned_state r1
  rw [eval_header_load _ _ table 0 keyLength t1 (by exact headerDomain 0 (by omega) (by omega)) (by exact inv.cell0)] at e2
  cases e2
  have t2 := (show (setVarHOLFinite (ofString "klen") (.val (.word keyLength))
      (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)).locals.lookup (ofString "t") =
      some (.val (.word table)) by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t1 ⊢
    exact t1)
  obtain ⟨v3,i3,e3,r3,m3,a3,b3,c3⟩ := dec_returned_state r2
  rw [eval_header_load _ _ table 8 stride t2 (by exact headerDomain 8 (by omega) (by omega)) (by exact inv.cell8)] at e3
  cases e3
  obtain ⟨v4,i4,e4,r4,m4,a4,b4,c4⟩ := dec_returned_state r3
  rw [eval_header_load _ _ table 32 keys
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 32 (by omega) (by omega)) (by exact inv.cell32)] at e4
  cases e4
  obtain ⟨v5,i5,e5,r5,m5,a5,b5,c5⟩ := dec_returned_state r4
  rw [eval_header_load _ _ table 48 used
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 48 (by omega) (by omega)) (by exact inv.cell48)] at e5
  cases e5
  obtain ⟨v6,i6,e6,r6,m6,a6,b6,c6⟩ := dec_returned_state r5
  rw [eval_header_load _ _ table 56 order
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 56 (by omega) (by omega)) (by exact inv.cell56)] at e6
  cases e6
  obtain ⟨v7,i7,e7,r7,m7,a7,b7,c7⟩ := dec_returned_state r6
  rw [eval_header_load _ _ table 64 orderPos
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 64 (by omega) (by omega)) (by exact inv.cell64)] at e7
  cases e7
  generalize hs7 : setVarHOLFinite (ofString "order_pos") (.val (.word orderPos)) (setVarHOLFinite (ofString "order") (.val (.word order))
    (setVarHOLFinite (ofString "used") (.val (.word used)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
      (setVarHOLFinite (ofString "stride") (.val (.word stride)) (setVarHOLFinite (ofString "klen") (.val (.word keyLength))
        (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)))))) = s7 at r7
  have s7Locals : InsertLocals s7 table key value capacity keyLength stride keys used order orderPos := by
    rw [← hs7]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal,keyLocal,valueLocal] 
  have s7Facts : s7.memory = state.memory ∧ s7.memaddrs = state.memaddrs ∧ s7.be = state.be ∧ s7.code = state.code ∧
      s7.clock = state.clock := by
    rw [← hs7]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨tL,kL,vL,capL,lenL,strideL,keysL,usedL,orderL,orderPosL⟩ := s7Locals
  obtain ⟨values',body,callee,returnShape,w,bodyPost,resumed,inner,args,lookup,bodyRun,rm,ra,rb,rc,rclk,rh,ragree,
    rrun,im,ia,ib,ic⟩ := decCall_returned_body r7
  have argsExact : evalListHOLFinite s7 (h := fun a => Classical.propDecidable (s7.memaddrs a))
      [.var .local (ofString "key"),.var .local (ofString "klen")] = some [.val (.word key),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,kL,lenL]
  rw [argsExact] at args
  cases args
  have installed : s7.code.lookup (ofString "htab_hash") =
      some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
    rw [s7Facts.2.2.2.1,inv.code]; exact originalRuntimeCode_hash_lookup
  rw [pan_two_word_lookup s7.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
    (sourceFunctionBody Guest.guestFn_htab_hash) key keyLength (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite s7 ((HolFiniteMapExact.empty.update (ofString "p",.val (.word key))).update
    (ofString "key_len",.val (.word keyLength))) = entry at bodyRun rclk
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨s7Facts.1,s7Facts.2.1,s7Facts.2.2.1,s7Facts.2.2.2.1,by rw [← s7Facts.2.2.2.2]; rfl⟩
  have hashBound := evaluate_htabHash_body_bounded entry (entryFacts.2.2.2.1.trans inv.code) keyLength
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by omega)
    (by rw [entryFacts.2.2.2.2]; omega)
  unfold RunBounded at hashBound
  rw [bodyRun] at hashBound
  obtain ⟨hb1,hb2,_⟩ := hashBound
  dsimp only at hb1 hb2
  have hashMemory := evaluate_readOnly_memory _ htabHash_readOnly entry
  have hashMeta := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_hash)
  rw [bodyRun] at hashMemory hashMeta
  have resumedFacts : resumed.memory = state.memory ∧ resumed.memaddrs = state.memaddrs ∧ resumed.be = state.be ∧
      resumed.code = state.code ∧ state.clock ≤ resumed.clock + (keyLength.toNat / 8 + 8 + 1) := by
    refine ⟨rm.trans (hashMemory.trans entryFacts.1),ra.trans (hashMeta.2.1.trans entryFacts.2.1),
      rb.trans (hashMeta.2.2.1.trans entryFacts.2.2.1),rc.trans (hashMeta.1.trans entryFacts.2.2.2.1),?_⟩
    have := rclk hb2
    have := entryFacts.2.2.2.2
    omega
  have resumedLocals : InsertLocals resumed table key value capacity keyLength stride keys used order orderPos := by
    apply InsertLocals.transfer (s := s7) ⟨tL,kL,vL,capL,lenL,strideL,keysL,usedL,orderL,orderPosL⟩
    intro k member
    apply ragree
    intro e
    subst e
    revert member
    decide
  obtain ⟨tR,kR,vR,capR,lenR,strideR,keysR,usedR,orderR,orderPosR⟩ := resumedLocals
  obtain ⟨indexValue,i8,e8,r8,m8,a8,b8,c8⟩ := dec_returned_state rrun
  obtain ⟨start,rfl,startInside⟩ := eval_hashFind_index_range resumed capacity bits inv.power capR indexValue e8
  generalize he : setVarHOLFinite (ofString "i") (.val (.word start)) resumed = e at r8
  have eLocals : InsertLocals e table key value capacity keyLength stride keys used order orderPos := by
    rw [← he]; exact InsertLocals.setVar ⟨tR,kR,vR,capR,lenR,strideR,keysR,usedR,orderR,orderPosR⟩ _ _ (by decide)
  have eIndex : e.locals.lookup (ofString "i") = some (.val (.word start)) := by
    rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eFacts : e.memory = state.memory ∧ e.memaddrs = state.memaddrs ∧ e.be = state.be ∧ e.code = state.code ∧
      e.clock = resumed.clock := by
    rw [← he]; exact ⟨resumedFacts.1,resumedFacts.2.1,resumedFacts.2.2.1,resumedFacts.2.2.2.1,rfl⟩
  have readSame : ∀ {G : Type} (r : PanSemStateFiniteExact 64 G), r.memory = state.memory → r.memaddrs = state.memaddrs →
      r.be = state.be → ∀ slot, hashOccupancyRead r used slot = hashOccupancyRead state used slot := by
    intro G r hm ha hb slot
    unfold hashOccupancyRead
    rw [hm,ha,hb]
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← inv.agreement]; exact room)
  obtain ⟨tE,kE,vE,capE,lenE,strideE,keysE,usedE,orderE,orderPosE⟩ := eLocals
  rw [evaluateHOLFiniteState_seq_line780] at r8
  have loopBound := hashInsertLoop_run capacity used empty keyLength bits inv.power emptyInside capacity.toNat e
    (eFacts.2.2.2.1.trans inv.code)
    ⟨capE,usedE,lenE,⟨keys,keysE⟩,⟨stride,strideE⟩,⟨key,kE⟩,
      by have := readSame e eFacts.1 eFacts.2.1 eFacts.2.2.1 empty; unfold hashOccupancyRead at this emptyRead; rw [this]; exact emptyRead,
      start,eIndex,startInside,Nat.le_of_lt (hashProbeDistance_lt_capacity _ _ _ startInside emptyInside)⟩
    (by rw [eFacts.2.2.2.2]; have := resumedFacts.2.2.2.2; omega)
  cases loopRun : evaluateHOLFiniteState e (.while (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))) with
  | mk loopResult m =>
    rw [loopRun] at r8 loopBound
    obtain ⟨lb1,_,_,_⟩ := loopBound
    dsimp only at lb1
    cases loopResult with
    | some r =>
      exfalso
      simp only at r8
      obtain ⟨er,_⟩ := Prod.mk.inj r8
      simp only [Option.some.injEq] at er
      subst er
      exact while_returned_invariant (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))
        (fun _ => True) (fun _ => False) (fun _ _ => trivial)
        (fun s v post _ run => absurd (congrArg Prod.fst run) (hashProbeStep_not_returned s _ v))
        (fun _ _ _ _ => trivial) e.clock e rfl trivial v m loopRun
    | none =>
      simp only at r8
      have exit := while_normal_exit (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))
        (fun {G} (s : PanSemStateFiniteExact 64 G) => s.memory = state.memory ∧ s.memaddrs = state.memaddrs ∧
          s.be = state.be ∧ s.code = state.code ∧
          InsertLocals s table key value capacity keyLength stride keys used order orderPos ∧
          ∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat < capacity.toNat)
        (fun s h => h)
        (by
          intro G s post ⟨sm,sa,sb,sc,sl,index,iL,inside⟩ flow
          have stepRun := evaluate_hashProbeStep s (ofString "i") index capacity iL sl.2.2.2.1
          rcases flow with normal | cont
          · rw [stepRun] at normal
            cases normal
            refine ⟨sm,sa,sb,sc,InsertLocals.setVar sl _ _ (by decide),hashProbeNext index capacity,
              by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],?_⟩
            rw [hashProbeNext_toNat index capacity bits inv.power inside]
            exact Nat.mod_lt _ capPos
          · rw [stepRun] at cont; cases cont)
        (fun s => hashProbeStep_not_break s _)
        e.clock e rfl ⟨eFacts.1,eFacts.2.1,eFacts.2.2.1,eFacts.2.2.2.1,⟨tE,kE,vE,capE,lenE,strideE,keysE,usedE,orderE,orderPosE⟩,
          start,eIndex,startInside⟩ m loopRun
      obtain ⟨⟨mm,ma,mb,mc,mLocals,slot,slotL,slotInside⟩,mZero⟩ := exit
      have slotEmpty : hashOccupancyRead state used slot = some 0 := by
        rw [← readSame m mm ma mb slot]
        exact hashProbeOccupied_zero_read m slot used slotL mLocals.2.2.2.2.2.2.2.1 mZero
      obtain ⟨tM,kM,vM,capM,lenM,strideM,keysM,usedM,orderM,orderPosM⟩ := mLocals
      -- layout arithmetic
      have kb := inv.keysBefore
      have vb := inv.valuesBefore
      have ub := inv.usedBefore
      have ob := inv.orderBefore
      have eb := inv.endBound
      have hk := inv.headerKeys
      have hv := inv.headerValues
      have fitsK := inv.fits
      have slotStride : slot.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ slotInside
      have dstNat : (keys + slot * stride).toNat = keys.toNat + slot.toNat * stride.toNat :=
        word_mul_add_toNat keys slot stride (by omega)
      have dstAligned : (keys + slot * stride).toNat % 8 = 0 := by
        rw [dstNat]
        have : slot.toNat * stride.toNat % 8 = 0 := by rw [Nat.mul_mod,inv.strideAligned]; simp
        have := inv.keysAligned
        omega
      have eight : (8 : BitVec 64).toNat = 8 := rfl
      have valueNat : (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
        rw [word_mul_add_toNat values slot 8 (by rw [eight]; omega),eight]
      have orderNat : (order + count * 8).toNat = order.toNat + count.toNat * 8 := by
        rw [word_mul_add_toNat order count 8 (by rw [eight]; omega),eight]
      have orderPosNat : (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 := by
        rw [word_mul_add_toNat orderPos slot 8 (by rw [eight]; omega),eight]
      have byteNat : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
          (panByteAlignHOL (used + s')).toNat = (used.toNat + s'.toNat) / 8 * 8 := by
        intro s' inside'
        rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
      have byteRange : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
          used.toNat ≤ (panByteAlignHOL (used + s')).toNat ∧ (panByteAlignHOL (used + s')).toNat < used.toNat + capacity.toNat := by
        intro s' inside'
        rw [byteNat s' inside']
        have := inv.usedAligned
        omega
      -- the copy call
      have copyArgs := eval_hashFind_comparison_args_exact m slot keys stride key keyLength slotL keysM strideM kM lenM
      rw [evaluateHOLFiniteState_seq_line780] at r8
      cases copyRun : evaluateHOLFiniteState m (.call (some (none,none)) (ofString "memcpy")
          [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]) with
      | mk copyResult c =>
        rw [copyRun] at r8
        cases copyResult with
        | some r =>
          exfalso
          simp only at r8
          obtain ⟨er,_⟩ := Prod.mk.inj r8
          simp only [Option.some.injEq] at er
          subst er
          exact discard_call_not_returned m _ _ v (by rw [copyRun])
        | none =>
          simp only at r8
          have mClock : keyLength.toNat / 32 + keyLength.toNat / 8 + 11 ≤ m.clock := by
            have := resumedFacts.2.2.2.2
            have := eFacts.2.2.2.2
            omega
          have copyFrame : ∀ watched : BitVec 64,
              (watched.toNat < (keys + slot * stride).toNat ∨ (keys + slot * stride).toNat + keyLength.toNat ≤ watched.toNat) →
              c.memory watched = state.memory watched := by
            intro watched outside
            have separated := memcpy_interval_separate (keys + slot * stride) keyLength watched dstAligned
              (by rw [dstNat]; omega) outside
            rw [memcpy_call_normal_memory m c _ (keys + slot * stride) key keyLength watched copyArgs
              (mc.trans inv.code) (fun o ho => (separated o ho).1) (fun o ho => (separated o ho).2) small mClock copyRun,mm]
          have copyMeta := evaluateHOLFiniteState_metadata m (.call (some (none,none)) (ofString "memcpy")
            [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")])
          rw [copyRun] at copyMeta
          have copyLocal : ∀ k : MlS, c.locals.lookup k = m.locals.lookup k := by
            intro k
            have kept := evaluate_avoidsLocal_flowing k (.call (some (none,none)) (ofString "memcpy")
              [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]) (by simp [avoidsLocal]) m
              (by rw [copyRun]; exact Or.inl rfl)
            rw [copyRun] at kept
            exact kept
          have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 := header 24 (by omega)
          have h40 : (table + 40 : BitVec 64).toNat = table.toNat + 40 := header 40 (by omega)
          have cAddr : c.memaddrs = state.memaddrs := copyMeta.2.1.trans ma
          have cBe : c.be = state.be := copyMeta.2.2.1.trans mb
          have cDomain : ∀ address : BitVec 64, address.toNat % 8 = 0 → table.toNat ≤ address.toNat →
              address.toNat < orderPos.toNat + capacity.toNat * 8 → c.memaddrs address := by
            intro address a1 a2 a3; rw [cAddr]; exact inv.domain address a1 a2 a3
          have headerMem : ∀ k : Nat, k ≤ 64 → c.memory (table + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
            intro k hk'
            apply copyFrame
            left; rw [header k hk',dstNat]; omega
          have byteMem : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
              c.memory (panByteAlignHOL (used + s')) = state.memory (panByteAlignHOL (used + s')) := by
            intro s' inside'
            apply copyFrame
            right; rw [dstNat]; have := byteRange s' inside'; omega
          have cRead : ∀ s' : BitVec 64, s'.toNat < capacity.toNat → hashOccupancyRead c used s' = hashOccupancyRead state used s' :=
            fun s' inside' => occupancyRead_congr_at c state used s' (byteMem s' inside') cAddr cBe
          obtain ⟨cell,hcell⟩ : ∃ cell : BitVec 64, c.memory (panByteAlignHOL (used + slot)) = .word cell := by
            cases h : c.memory (panByteAlignHOL (used + slot)) with
            | word x => exact ⟨x,rfl⟩
          have ready : HashInsertTailReady capacity used table values value order orderPos count slot cell c := {
            tableLocal := (copyLocal _).trans tM
            orderLocal := (copyLocal _).trans orderM
            orderPosLocal := (copyLocal _).trans orderPosM
            usedLocal := (copyLocal _).trans usedM
            indexLocal := (copyLocal _).trans slotL
            valueLocal := (copyLocal _).trans vM
            inside := slotInside
            valuesDomain := cDomain _ (by rw [h40]; have := inv.tableAligned; omega)
              (by rw [h40]; omega) (by rw [h40]; omega)
            valuesMemory := (headerMem 40 (by omega)).trans inv.cell40
            valueDomain := cDomain _ (by rw [valueNat]; have := inv.valuesAligned; omega) (by rw [valueNat]; omega)
              (by rw [valueNat]; omega)
            byteDomain := cDomain _ (by rw [byteNat slot slotInside]; omega)
              (by have := byteRange slot slotInside; omega) (by have := byteRange slot slotInside; omega)
            byteMemory := hcell
            empty := (cRead slot slotInside).trans slotEmpty
            orderDomain := cDomain _ (by rw [orderNat]; have := inv.orderAligned; omega) (by rw [orderNat]; omega)
              (by rw [orderNat]; omega)
            orderPosDomain := cDomain _ (by rw [orderPosNat]; have := inv.orderPosAligned; omega) (by rw [orderPosNat]; omega)
              (by rw [orderPosNat]; omega)
            countDomain := cDomain _ (by rw [h24]; have := inv.tableAligned; omega)
              (by rw [h24]; omega) (by rw [h24]; omega)
            countMemory := (headerMem 24 (by omega)).trans inv.cell24
            agreement := by
              rw [inv.agreement]
              exact hashOccupiedCount_congr capacity _ _ (fun s' inside' => (cRead s' inside').symm)
            noWrap := by have := count.isLt; omega
            valueCountSeparate := word_ne_of_toNat (by rw [h24,valueNat]; omega)
            valueSeparate := fun s' inside' => word_ne_of_toNat (by rw [valueNat]; have := byteRange s' inside'; omega)
            separate := fun s' inside' => ⟨word_ne_of_toNat (by rw [orderNat]; have := byteRange s' inside'; omega),
              word_ne_of_toNat (by rw [orderPosNat]; have := byteRange s' inside'; omega),
              word_ne_of_toNat (by rw [h24]; have := byteRange s' inside'; omega)⟩ }
          obtain ⟨tailPost,tailRun,p24,pAgree,_,_,pCode,pAddr,pBe,pFrame⟩ := ready.run_memory
          rw [htabInsertRawFinish_eq,tailRun] at r8
          obtain ⟨_,hp⟩ := Prod.mk.inj r8
          subst hp
          have postMem : post.memory = tailPost.memory :=
            m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans (im.trans m8)))))))
          have postAddr : post.memaddrs = state.memaddrs :=
            (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (ia.trans a8)))))))).trans (pAddr.trans cAddr)
          have postBe : post.be = state.be :=
            (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans (ib.trans b8)))))))).trans (pBe.trans cBe)
          have postCode : post.code = originalRuntimeCode :=
            (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (ic.trans c8)))))))).trans
              (pCode.trans (copyMeta.1.trans (mc.trans inv.code)))
          have untouched : ∀ watched : BitVec 64, watched ≠ values + slot * 8 → watched ≠ panByteAlignHOL (used + slot) →
              watched ≠ order + count * 8 → watched ≠ orderPos + slot * 8 → watched ≠ table + 24 →
              (watched.toNat < (keys + slot * stride).toNat ∨ (keys + slot * stride).toNat + keyLength.toNat ≤ watched.toNat) →
              post.memory watched = state.memory watched := by
            intro watched n1 n2 n3 n4 n5 outside
            rw [postMem,pFrame watched n1 n2 n3 n4 n5,copyFrame watched outside]
          have byteSlot := byteRange slot slotInside
          have cellKeep : ∀ k : Nat, k ≤ 64 → k ≠ 24 → post.memory (table + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
            intro k hk' ne24
            apply untouched
            · exact word_ne_of_toNat (by rw [header k hk',valueNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk']; omega)
            · exact word_ne_of_toNat (by rw [header k hk',orderNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk',orderPosNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk',h24]; omega)
            · left; rw [header k hk',dstNat]; omega
          refine ⟨{
            code := postCode
            power := inv.power
            tableAligned := inv.tableAligned
            keysAligned := inv.keysAligned
            strideAligned := inv.strideAligned
            valuesAligned := inv.valuesAligned
            usedAligned := inv.usedAligned
            orderAligned := inv.orderAligned
            orderPosAligned := inv.orderPosAligned
            headerKeys := inv.headerKeys
            headerValues := inv.headerValues
            keysBefore := inv.keysBefore
            valuesBefore := inv.valuesBefore
            usedBefore := inv.usedBefore
            orderBefore := inv.orderBefore
            endBound := inv.endBound
            fits := inv.fits
            domain := fun address a1' a2' a3' => by rw [postAddr]; exact inv.domain address a1' a2' a3'
            cell0 := (cellKeep 0 (by omega) (by omega)).trans inv.cell0
            cell8 := (cellKeep 8 (by omega) (by omega)).trans inv.cell8
            cell16 := (cellKeep 16 (by omega) (by omega)).trans inv.cell16
            cell24 := by rw [postMem]; exact p24
            cell32 := (cellKeep 32 (by omega) (by omega)).trans inv.cell32
            cell40 := (cellKeep 40 (by omega) (by omega)).trans inv.cell40
            cell48 := (cellKeep 48 (by omega) (by omega)).trans inv.cell48
            cell56 := (cellKeep 56 (by omega) (by omega)).trans inv.cell56
            cell64 := (cellKeep 64 (by omega) (by omega)).trans inv.cell64
            agreement := by
              rw [pAgree]
              apply hashOccupiedCount_congr
              intro s' _
              exact (occupancyRead_congr_at post tailPost used s' (by rw [postMem])
                (postAddr.trans (pAddr.trans cAddr).symm) (postBe.trans (pBe.trans cBe).symm)).symm },
            postAddr,postBe,?_⟩
          intro watched outside
          apply untouched
          · exact word_ne_of_toNat (by rw [valueNat]; omega)
          · exact word_ne_of_toNat (by omega)
          · exact word_ne_of_toNat (by rw [orderNat]; omega)
          · exact word_ne_of_toNat (by rw [orderPosNat]; omega)
          · exact word_ne_of_toNat (by rw [h24]; omega)
          · rw [dstNat]; omega
#print axioms htabInsertRaw_returned_aligned
end InitECandidate.Runtime
