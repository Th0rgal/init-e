import InitECandidate.Runtime.HtabSetFrame
import InitECandidate.Runtime.OriginalHashDeleteCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

open InitECandidate.Proofs.FrontendCodecComputation in
def htabDelDecoded : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_del with | .function fn => fn.body | _ => .skip

/-- The backward-shift loop body. -/
def htabDelBody : ProgHOL 64 :=
  match htabDelDecoded with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _)))))))))))) => body
  | _ => .skip

/-- Everything after the backward-shift loop. -/
def htabDelTail : ProgHOL 64 :=
  match htabDelDecoded with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ tail)))))))))))) => tail
  | _ => .skip

def htabDelMissing : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "i")) (.var .local (ofString "cap"))) (.return (.const 0)) .skip

theorem source_htabDel_body : sourceFunctionBody Guest.guestFn_htab_del =
    .decCall (ofString "i") .one (ofString "htab_find_slot") [.var .local (ofString "t"),.var .local (ofString "key")]
    (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "t"),.const 16]))
    (.seq htabDelMissing
    (.dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"),.const 0]))
    (.dec (ofString "stride") .one (.load .one (.op .add [.var .local (ofString "t"),.const 8]))
    (.dec (ofString "keys") .one (.load .one (.op .add [.var .local (ofString "t"),.const 32]))
    (.dec (ofString "vals") .one (.load .one (.op .add [.var .local (ofString "t"),.const 40]))
    (.dec (ofString "used") .one (.load .one (.op .add [.var .local (ofString "t"),.const 48]))
    (.dec (ofString "order") .one (.load .one (.op .add [.var .local (ofString "t"),.const 56]))
    (.dec (ofString "order_pos") .one (.load .one (.op .add [.var .local (ofString "t"),.const 64]))
    (.dec (ofString "deleted_pos") .one (.load .one (.op .add [.var .local (ofString "order_pos"),
        .panop .mul [.var .local (ofString "i"),.const 8]]))
    (.dec (ofString "j") .one (.var .local (ofString "i"))
    (.seq (.while (.const 1) htabDelBody) htabDelTail)))))))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl


def htabDelMovable : ProgHOL 64 :=
  match htabDelBody with
  | .seq _ (.seq _ (.decCall _ _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq m _))))) => m
  | _ => .skip

def htabDelMove : ProgHOL 64 :=
  match htabDelBody with
  | .seq _ (.seq _ (.decCall _ _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.ite _ mv _)))))) => mv
  | _ => .skip

def htabDelMoveRest : ProgHOL 64 :=
  match htabDelMove with
  | .seq _ (.seq _ (.dec _ _ _ rest)) => rest
  | _ => .skip

theorem htabDelBody_shape : htabDelBody =
    .seq (hashProbeStep (ofString "j"))
      (.seq (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip)
        (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")]
          (.dec (ofString "home") .one (.op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]])
            (.dec (ofString "movable") .one (.const 0)
              (.seq htabDelMovable
                (.ite (.cmp .notEqual (.var .local (ofString "movable")) (.const 0)) htabDelMove .skip)))))) := rfl

theorem htabDelMove_shape : htabDelMove =
    .seq (.call (some (none,none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
         .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
         .var .local (ofString "klen")])
      (.seq (.store (.op .add [.var .local (ofString "vals"),.panop .mul [.var .local (ofString "i"),.const 8]])
          (.load .one (.op .add [.var .local (ofString "vals"),.panop .mul [.var .local (ofString "j"),.const 8]])))
        (.dec (ofString "moved_pos") .one
            (.load .one (.op .add [.var .local (ofString "order_pos"),.panop .mul [.var .local (ofString "j"),.const 8]]))
          htabDelMoveRest)) := rfl

theorem htabDelMoveRest_shape : htabDelMoveRest =
    .seq (.store (.op .add [.var .local (ofString "order"),.panop .mul [.var .local (ofString "moved_pos"),.const 8]])
        (.var .local (ofString "i")))
      (.seq (.store (.op .add [.var .local (ofString "order_pos"),.panop .mul [.var .local (ofString "i"),.const 8]])
          (.var .local (ofString "moved_pos")))
        (.assign .local (ofString "i") (.var .local (ofString "j")))) := rfl

theorem htabDelMovable_straight : extStraightLine htabDelMovable = true := by decide
theorem htabDelMovable_readOnly : readOnlyMemory htabDelMovable = true := by decide

/-- Occupied slots have order-position entries inside the table. -/
def OrderPosBounded {F : Type} (s : PanSemStateFiniteExact 64 F) (capacity used orderPos : BitVec 64) : Prop :=
  ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead s used q ≠ some 0 →
    ∃ x : BitVec 64, s.memory (orderPos + q * 8) = .word x ∧ x.toNat < capacity.toNat

/-- Backward-shift loop state: the aligned table with its header locals, the
cursors i, j in range, a known empty slot, and bounded order positions. -/
structure DelState {F : Type} (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64)
    (bits : Nat) (occ : BitVec 64 → Option UInt8) (s : PanSemStateFiniteExact 64 F) (I J : BitVec 64) : Prop where
  inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s
  emptyInside : empty.toNat < capacity.toNat
  bytes : ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead s used q = occ q
  emptyByte : occ empty = some 0
  orderPosOK : OrderPosBounded s capacity used orderPos
  capL : s.locals.lookup (ofString "cap") = some (.val (.word capacity))
  usedL : s.locals.lookup (ofString "used") = some (.val (.word used))
  keysL : s.locals.lookup (ofString "keys") = some (.val (.word keys))
  strideL : s.locals.lookup (ofString "stride") = some (.val (.word stride))
  klenL : s.locals.lookup (ofString "klen") = some (.val (.word keyLength))
  valsL : s.locals.lookup (ofString "vals") = some (.val (.word values))
  orderL : s.locals.lookup (ofString "order") = some (.val (.word order))
  orderPosL : s.locals.lookup (ofString "order_pos") = some (.val (.word orderPos))
  iL : s.locals.lookup (ofString "i") = some (.val (.word I))
  jL : s.locals.lookup (ofString "j") = some (.val (.word J))
  iInside : I.toNat < capacity.toNat
  jInside : J.toNat < capacity.toNat

theorem eval_delBreakCheck {F : Type} (s : PanSemStateFiniteExact 64 F) (used J : BitVec 64) (byte : UInt8)
    (usedL : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (jL : s.locals.lookup (ofString "j") = some (.val (.word J)))
    (loaded : hashOccupancyRead s used J = some byte) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0)) =
        some (.val (.word (if byte = 0 then 1 else 0))) := by
  unfold hashOccupancyRead at loaded
  simp [evalHOLExact,evalListHOLExact,usedL,jL,wordOpHOL,wordOp,valueIsWord,valueWord,loaded,
    Compiler.Encoders.Asm.wordCmpHOL]
  by_cases b : byte = 0
  · simp [b]
  · have : (BitVec.ofNat 64 byte.toNat) ≠ 0 := by
      intro h
      apply b
      have h2 : byte.toNat = 0 := by
        have := congrArg BitVec.toNat h
        have small : byte.toNat < 2 ^ 64 := by have := byte.toNat_lt; omega
        simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using this
      exact UInt8.toNat_inj.mp h2
    simp [b]
    exact this

#print axioms eval_delBreakCheck

/-- Address arithmetic for the table regions of an aligned table. -/
theorem HtabAligned.slot_toNat {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (q : BitVec 64) (inside : q.toNat < capacity.toNat) :
    (values + q * 8).toNat = values.toNat + q.toNat * 8 ∧ (order + q * 8).toNat = order.toNat + q.toNat * 8 ∧
      (orderPos + q * 8).toNat = orderPos.toNat + q.toNat * 8 ∧
      (keys + q * stride).toNat = keys.toNat + q.toNat * stride.toNat ∧
      q.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
  have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore; have eb := inv.endBound
  have kb := inv.keysBefore
  have mono : q.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ inside
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  refine ⟨?_,?_,?_,?_,mono⟩
  · rw [word_mul_add_toNat values q 8 (by rw [eight]; omega),eight]
  · rw [word_mul_add_toNat order q 8 (by rw [eight]; omega),eight]
  · rw [word_mul_add_toNat orderPos q 8 (by rw [eight]; omega),eight]
  · exact word_mul_add_toNat keys q stride (by omega)

#print axioms HtabAligned.slot_toNat

def delLocalNames : List MlS :=
  [ofString "cap",ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "vals",ofString "order",
    ofString "order_pos",ofString "i",ofString "j"]

/-- The backward-shift state transfers to any state agreeing on the header,
occupancy and order-position cells, the address map, endianness, code and the
tracked locals. -/
theorem DelState.congr {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (header : ∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k))
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + slot)) = s.memory (panByteAlignHOL (used + slot)))
    (positions : ∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (orderPos + q * 8) = s.memory (orderPos + q * 8))
    (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) (code : r.code = s.code)
    (locals : ∀ k ∈ delLocalNames, r.locals.lookup k = s.locals.lookup k) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ r I J := by
  have inv := d.inv
  have read : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead r used slot = hashOccupancyRead s used slot :=
    fun slot inside => occupancyRead_congr_at r s used slot (occupancy slot inside) addresses endian
  simp only [delLocalNames,List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp,forall_eq] at locals
  obtain ⟨l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := locals
  have h : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k) = (table + BitVec.ofNat 64 k) := fun _ _ => rfl
  exact {
    inv := {
      code := code.trans inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
      strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
      orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned, headerKeys := inv.headerKeys,
      headerValues := inv.headerValues, keysBefore := inv.keysBefore, valuesBefore := inv.valuesBefore,
      usedBefore := inv.usedBefore, orderBefore := inv.orderBefore, endBound := inv.endBound, fits := inv.fits,
      domain := fun a h1 h2 h3 => by rw [addresses]; exact inv.domain a h1 h2 h3,
      cell0 := (header 0 (by omega)).trans inv.cell0, cell8 := (header 8 (by omega)).trans inv.cell8,
      cell16 := (header 16 (by omega)).trans inv.cell16, cell24 := (header 24 (by omega)).trans inv.cell24,
      cell32 := (header 32 (by omega)).trans inv.cell32, cell40 := (header 40 (by omega)).trans inv.cell40,
      cell48 := (header 48 (by omega)).trans inv.cell48, cell56 := (header 56 (by omega)).trans inv.cell56,
      cell64 := (header 64 (by omega)).trans inv.cell64,
      agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot inside => (read slot inside).symm) }
    emptyInside := d.emptyInside
    bytes := fun q inside => (read q inside).trans (d.bytes q inside)
    emptyByte := d.emptyByte
    orderPosOK := fun q inside occupied => by
      rw [positions q inside]
      exact d.orderPosOK q inside (by rw [← read q inside]; exact occupied)
    capL := l1.trans d.capL, usedL := l2.trans d.usedL, keysL := l3.trans d.keysL, strideL := l4.trans d.strideL,
    klenL := l5.trans d.klenL, valsL := l6.trans d.valsL, orderL := l7.trans d.orderL, orderPosL := l8.trans d.orderPosL,
    iL := l9.trans d.iL, jL := l10.trans d.jL, iInside := d.iInside, jInside := d.jInside }

#print axioms DelState.congr

/-- Core transfer with the new order positions given directly; the backward-shift state transfers to any state agreeing on the header,
occupancy and order-position cells, the address map, endianness, code and the
tracked locals. -/
theorem DelState.congrCore {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (header : ∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k))
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + slot)) = s.memory (panByteAlignHOL (used + slot)))
    (positionsOK : OrderPosBounded r capacity used orderPos)
    (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) (code : r.code = s.code)
    (locals : ∀ k ∈ delLocalNames, r.locals.lookup k = s.locals.lookup k) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ r I J := by
  have inv := d.inv
  have read : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead r used slot = hashOccupancyRead s used slot :=
    fun slot inside => occupancyRead_congr_at r s used slot (occupancy slot inside) addresses endian
  simp only [delLocalNames,List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp,forall_eq] at locals
  obtain ⟨l1,l2,l3,l4,l5,l6,l7,l8,l9,l10⟩ := locals
  have h : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k) = (table + BitVec.ofNat 64 k) := fun _ _ => rfl
  exact {
    inv := {
      code := code.trans inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
      strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
      orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned, headerKeys := inv.headerKeys,
      headerValues := inv.headerValues, keysBefore := inv.keysBefore, valuesBefore := inv.valuesBefore,
      usedBefore := inv.usedBefore, orderBefore := inv.orderBefore, endBound := inv.endBound, fits := inv.fits,
      domain := fun a h1 h2 h3 => by rw [addresses]; exact inv.domain a h1 h2 h3,
      cell0 := (header 0 (by omega)).trans inv.cell0, cell8 := (header 8 (by omega)).trans inv.cell8,
      cell16 := (header 16 (by omega)).trans inv.cell16, cell24 := (header 24 (by omega)).trans inv.cell24,
      cell32 := (header 32 (by omega)).trans inv.cell32, cell40 := (header 40 (by omega)).trans inv.cell40,
      cell48 := (header 48 (by omega)).trans inv.cell48, cell56 := (header 56 (by omega)).trans inv.cell56,
      cell64 := (header 64 (by omega)).trans inv.cell64,
      agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot inside => (read slot inside).symm) }
    emptyInside := d.emptyInside
    bytes := fun q inside => (read q inside).trans (d.bytes q inside)
    emptyByte := d.emptyByte
    orderPosOK := positionsOK
    capL := l1.trans d.capL, usedL := l2.trans d.usedL, keysL := l3.trans d.keysL, strideL := l4.trans d.strideL,
    klenL := l5.trans d.klenL, valsL := l6.trans d.valsL, orderL := l7.trans d.orderL, orderPosL := l8.trans d.orderPosL,
    iL := l9.trans d.iL, jL := l10.trans d.jL, iInside := d.iInside, jInside := d.jInside }


/-- A write that misses the header, occupancy and order-position cells keeps the backward-shift state. -/
theorem DelState.write_region {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (address value : BitVec 64)
    (header : ∀ k : Nat, k ≤ 64 → address ≠ table + BitVec.ofNat 64 k)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → address ≠ panByteAlignHOL (used + slot))
    (positions : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ orderPos + q * 8) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
      (sourceWriteWord s address value) I J :=
  d.congr (fun k hk => by simp [sourceWriteWord]; intro h; first | exact absurd h (header k hk) | exact absurd h.symm (header k hk))
    (fun slot inside => by simp [sourceWriteWord]; intro h; first | exact absurd h (occupancy slot inside) | exact absurd h.symm (occupancy slot inside))
    (fun q inside => by simp [sourceWriteWord]; intro h; first | exact absurd h (positions q inside) | exact absurd h.symm (positions q inside)) rfl rfl rfl (fun _ _ => rfl)

/-- Writing an in-table order position for slot P keeps the backward-shift state. -/
theorem DelState.write_position {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (P value : BitVec 64) (pInside : P.toNat < capacity.toNat) (small : value.toNat < capacity.toNat) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
      (sourceWriteWord s (orderPos + P * 8) value) I J := by
  have inv := d.inv
  have pNat := (inv.slot_toNat P pInside).2.2.1
  have headerFar : ∀ k : Nat, k ≤ 64 → orderPos + P * 8 ≠ table + BitVec.ofNat 64 k := by
    intro k hk
    apply word_ne_of_toNat
    rw [pNat,word_add_toNat table k (by have := keys.isLt; have := inv.headerKeys; omega)]
    have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore; omega
  have occFar : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + P * 8 ≠ panByteAlignHOL (used + slot) := by
    intro slot inside
    apply word_ne_of_toNat
    rw [pNat,byteAlign_toNat,BitVec.toNat_add_of_lt (by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega)]
    have := inv.usedBefore; have := inv.orderBefore; omega
  have read : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead (sourceWriteWord s (orderPos + P * 8) value) used slot = hashOccupancyRead s used slot :=
    fun slot inside => occupancyRead_congr_at _ s used slot (by simp [sourceWriteWord]; intro h; first | exact absurd h (occFar slot inside) | exact absurd h.symm (occFar slot inside)) rfl rfl
  refine d.congrCore (fun k hk => by simp [sourceWriteWord]; intro h; first | exact absurd h (headerFar k hk) | exact absurd h.symm (headerFar k hk))
    (fun slot inside => by simp [sourceWriteWord]; intro h; first | exact absurd h (occFar slot inside) | exact absurd h.symm (occFar slot inside)) ?_ rfl rfl rfl (fun _ _ => rfl)
  intro q inside occupied
  by_cases same : q = P
  · subst same
    exact ⟨value,by simp [sourceWriteWord],small⟩
  · have qNat := (inv.slot_toNat q inside).2.2.1
    have ne : orderPos + q * 8 ≠ orderPos + P * 8 := by
      apply word_ne_of_toNat
      rw [qNat,pNat]
      intro h
      apply same
      apply BitVec.eq_of_toNat_eq
      omega
    have old := d.orderPosOK q inside (by rw [← read q inside]; exact occupied)
    simp only [sourceWriteWord,if_neg ne]
    exact old

#print axioms DelState.write_region
#print axioms DelState.write_position

theorem seq_normal_parts {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.seq a b) = (none,post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none,mid) ∧ evaluateHOLFiniteState mid b = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases first : evaluateHOLFiniteState s a with
  | mk result mid =>
    rw [first] at run
    cases result with
    | none => exact ⟨mid,rfl,run⟩
    | some r => simp at run

theorem eval_delScaled {F : Type} (s : PanSemStateFiniteExact 64 F) (base index scale : MlS) (b x m : BitVec 64)
    (bL : s.locals.lookup base = some (.val (.word b))) (xL : s.locals.lookup index = some (.val (.word x)))
    (mL : s.locals.lookup scale = some (.val (.word m))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base,.panop .mul [.var .local index,.var .local scale]]) = some (.val (.word (b + x * m))) := by
  simp [evalListHOLExact,evalHOLExact,bL,xL,mL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

theorem eval_delScaled8 {F : Type} (s : PanSemStateFiniteExact 64 F) (base index : MlS) (b x : BitVec 64)
    (bL : s.locals.lookup base = some (.val (.word b))) (xL : s.locals.lookup index = some (.val (.word x))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base,.panop .mul [.var .local index,.const 8]]) = some (.val (.word (b + x * 8))) := by
  simp [evalListHOLExact,evalHOLExact,bL,xL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

theorem eval_delLoad {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (address value : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word address)))
    (domain : s.memaddrs address) (cell : s.memory address = .word value) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) =
      some (.val (.word value)) := by
  simp only [evalHOLExact,isWfShapeExactHOL]
  rw [he]
  simp [memLoadHOLExact,domain,cell]

theorem eval_delVar {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (x : BitVec 64)
    (xL : s.locals.lookup name = some (.val (.word x))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local name) =
      some (.val (.word x)) := by
  simp [evalHOLExact,xL]

theorem evaluate_delAssign {F : Type} (s : PanSemStateFiniteExact 64 F) (name source : MlS) (x old : BitVec 64)
    (xL : s.locals.lookup source = some (.val (.word x))) (oldL : s.locals.lookup name = some (.val (.word old))) :
    evaluateHOLFiniteState s (.assign .local name (.var .local source)) =
      (none,setVarHOLFinite name (.val (.word x)) s) := by
  classical
  simp [evaluateHOLFiniteState_assign,evalHOLExact,xL,oldL,isValidValueHOLExact,
    lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

#print axioms seq_normal_parts
#print axioms evaluate_delAssign

/-- Setting a local outside the tracked names keeps the backward-shift state. -/
theorem DelState.setOther {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (name : MlS) (value : ValueHOL 64) (fresh : name ∉ delLocalNames) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ (setVarHOLFinite name value s) I J :=
  d.congr (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl (fun k member => by
    have ne : k ≠ name := fun h => fresh (h ▸ member)
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne])

/-- Setting the hole index to an in-table slot. -/
theorem DelState.setI {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (I' : BitVec 64) (inside : I'.toNat < capacity.toNat) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
      (setVarHOLFinite (ofString "i") (.val (.word I')) s) I' J := by
  have keep : ∀ k, k ≠ ofString "i" → (setVarHOLFinite (ofString "i") (.val (.word I')) s).locals.lookup k = s.locals.lookup k := by
    intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  exact { d with
    inv := { d.inv with }
    capL := (keep _ (by decide)).trans d.capL, usedL := (keep _ (by decide)).trans d.usedL,
    keysL := (keep _ (by decide)).trans d.keysL, strideL := (keep _ (by decide)).trans d.strideL,
    klenL := (keep _ (by decide)).trans d.klenL, valsL := (keep _ (by decide)).trans d.valsL,
    orderL := (keep _ (by decide)).trans d.orderL, orderPosL := (keep _ (by decide)).trans d.orderPosL,
    iL := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
    jL := (keep _ (by decide)).trans d.jL, iInside := inside }

#print axioms DelState.setOther
#print axioms DelState.setI

theorem delStride_mod {stride I : BitVec 64} (aligned : stride.toNat % 8 = 0) : (I.toNat * stride.toNat) % 8 = 0 := by
  rw [Nat.mul_mod,aligned,Nat.mul_zero,Nat.zero_mod]

/-- A normal backward-shift move from hole I to occupied slot J keeps the
state, with the hole moved to J. -/
theorem htabDelMove_normal {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (occupied : hashOccupancyRead s used J ≠ some 0)
    (budget : keyLength.toNat / 32 + keyLength.toNat / 8 + 11 ≤ s.clock)
    (run : evaluateHOLFiniteState s htabDelMove = (none,post)) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post J J := by
  have inv := d.inv
  have iN := inv.slot_toNat I d.iInside
  have jN := inv.slot_toNat J d.jInside
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have strideLe : stride.toNat ≤ capacity.toNat * stride.toNat := Nat.le_mul_of_pos_left _ capPos
  have kb := inv.keysBefore; have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have fits := inv.fits; have hk := inv.headerKeys; have hv := inv.headerValues
  have small : keyLength.toNat ≤ 33806089496 := by omega
  have iIn := d.iInside; have jIn := d.jInside
  rw [htabDelMove_shape] at run
  obtain ⟨c,copyRun,run⟩ := seq_normal_parts run
  -- the key copy
  have copyArgs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] =
        some [.val (.word (keys + I * stride)),.val (.word (keys + J * stride)),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,d.keysL,d.iL,d.jL,d.strideL,d.klenL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have dstAligned : (keys + I * stride).toNat % 8 = 0 := by
    rw [iN.2.2.2.1]; have := delStride_mod (I := I) inv.strideAligned; have := inv.keysAligned; omega
  have copyFrame : ∀ watched : BitVec 64,
      (watched.toNat < (keys + I * stride).toNat ∨ (keys + I * stride).toNat + keyLength.toNat ≤ watched.toNat) →
      c.memory watched = s.memory watched := by
    intro watched outside
    have separated := memcpy_interval_separate (keys + I * stride) keyLength watched dstAligned
      (by rw [iN.2.2.2.1]; have := iN.2.2.2.2; omega) outside
    exact memcpy_call_normal_memory s c _ (keys + I * stride) (keys + J * stride) keyLength watched copyArgs
      inv.code (fun o ho => (separated o ho).1) (fun o ho => (separated o ho).2) small budget copyRun
  have copyMeta := evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "memcpy")
    [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
     .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
     .var .local (ofString "klen")])
  rw [copyRun] at copyMeta
  have copyLocal : ∀ k : MlS, c.locals.lookup k = s.locals.lookup k := by
    intro k
    have kept := evaluate_avoidsLocal_flowing k (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")]) (by simp [avoidsLocal]) s (by rw [copyRun]; exact Or.inl rfl)
    rw [copyRun] at kept
    exact kept
  have iDst := iN.2.2.2.1; have iEnd := iN.2.2.2.2
  have byteNat : ∀ q : BitVec 64, q.toNat < capacity.toNat → (panByteAlignHOL (used + q)).toNat = (used.toNat + q.toNat) / 8 * 8 := by
    intro q inside
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  have dc : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ c I J :=
    d.congr
      (fun k hk' => copyFrame _ (Or.inl (by
        rw [word_add_toNat table k (by have := keys.isLt; omega),iDst]; omega)))
      (fun q inside => copyFrame _ (Or.inr (by
        rw [byteNat q inside,iDst]; have := inv.usedAligned; omega)))
      (fun q inside => copyFrame _ (Or.inr (by
        rw [(inv.slot_toNat q inside).2.2.1,iDst]; omega)))
      copyMeta.2.1 copyMeta.2.2.1 copyMeta.1 (fun k _ => copyLocal k)
  have cOcc : hashOccupancyRead c used J = hashOccupancyRead s used J :=
    occupancyRead_congr_at c s used J (copyFrame _ (Or.inr (by rw [byteNat J d.jInside,iDst]; have := inv.usedAligned; omega)))
      copyMeta.2.1 copyMeta.2.2.1
  -- the value move
  obtain ⟨c2,valRun,run⟩ := seq_normal_parts run
  have cInv := dc.inv
  have domainAt : ∀ base : BitVec 64, ∀ q : BitVec 64, base.toNat % 8 = 0 → table.toNat ≤ base.toNat →
      (base + q * 8).toNat = base.toNat + q.toNat * 8 → base.toNat + q.toNat * 8 < orderPos.toNat + capacity.toNat * 8 →
      c.memaddrs (base + q * 8) := by
    intro base q a1 a2 e a3
    exact cInv.domain _ (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨jv,hjv⟩ : ∃ x : BitVec 64, c.memory (values + J * 8) = .word x := by
    cases h : c.memory (values + J * 8) with
    | word x => exact ⟨x,rfl⟩
  have c2Eq := store_word_normal c c2 _ _ (values + I * 8) jv
    (eval_delScaled8 c _ _ values I dc.valsL dc.iL)
    (eval_delLoad c _ (values + J * 8) jv (eval_delScaled8 c _ _ values J dc.valsL dc.jL)
      (domainAt values J inv.valuesAligned (by omega) jN.1 (by omega)) hjv) valRun
  subst c2Eq
  have dc2 := dc.write_region (values + I * 8) jv
    (fun k hk' => by
      apply word_ne_of_toNat
      rw [iN.1,word_add_toNat table k (by have := values.isLt; omega)]; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [iN.1,byteNat q inside]; have := inv.usedAligned; have := inv.valuesAligned; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [iN.1,(inv.slot_toNat q inside).2.2.1]; omega)
  have c2Occ : hashOccupancyRead (sourceWriteWord c (values + I * 8) jv) used J ≠ some 0 := by
    rw [occupancyRead_congr_at (sourceWriteWord c (values + I * 8) jv) c used J (by
      simp only [sourceWriteWord]
      rw [if_neg]
      intro h
      have := congrArg BitVec.toNat h
      rw [iN.1,byteNat J d.jInside] at this
      have := inv.usedAligned; have := inv.valuesAligned; omega) rfl rfl,cOcc]
    exact occupied
  generalize sourceWriteWord c (values + I * 8) jv = c2 at dc2 c2Occ run
  -- the moved order position
  obtain ⟨value,inner,hval,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state run
  obtain ⟨x,hx,xlt⟩ := dc2.orderPosOK J jIn c2Occ
  have inv2 := dc2.inv
  rw [eval_delLoad c2 _ (orderPos + J * 8) x (eval_delScaled8 c2 _ _ orderPos J dc2.orderPosL dc2.jL)
    (inv2.domain _ (by rw [jN.2.2.1]; have := inv.orderPosAligned; omega) (by rw [jN.2.2.1]; omega)
      (by rw [jN.2.2.1]; omega)) hx] at hval
  cases hval
  have dc3 := dc2.setOther (ofString "moved_pos") (.val (.word x)) (by decide)
  have movedL : (setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2).locals.lookup (ofString "moved_pos") =
      some (.val (.word x)) := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  generalize setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2 = c3 at dc3 movedL innerRun
  rw [htabDelMoveRest_shape] at innerRun
  obtain ⟨c4,orderRun,innerRun⟩ := seq_normal_parts innerRun
  have c4Eq := store_word_normal c3 c4 _ _ (order + x * 8) I
    (eval_delScaled8 c3 _ _ order x dc3.orderL movedL) (eval_delVar c3 _ I dc3.iL) orderRun
  subst c4Eq
  have xN := inv.slot_toNat x xlt
  have dc4 := dc3.write_region (order + x * 8) I
    (fun k hk' => by
      apply word_ne_of_toNat
      rw [xN.2.1,word_add_toNat table k (by have := values.isLt; omega)]; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [xN.2.1,byteNat q inside]; have := inv.usedAligned; have := inv.orderAligned; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [xN.2.1,(inv.slot_toNat q inside).2.2.1]; omega)
  have movedL4 : (sourceWriteWord c3 (order + x * 8) I).locals.lookup (ofString "moved_pos") = some (.val (.word x)) := movedL
  generalize sourceWriteWord c3 (order + x * 8) I = c4 at dc4 movedL4 innerRun
  obtain ⟨c5,posRun,assignRun⟩ := seq_normal_parts innerRun
  have c5Eq := store_word_normal c4 c5 _ _ (orderPos + I * 8) x
    (eval_delScaled8 c4 _ _ orderPos I dc4.orderPosL dc4.iL) (eval_delVar c4 _ x movedL4) posRun
  subst c5Eq
  have dc5 := dc4.write_position I x iIn xlt
  generalize sourceWriteWord c4 (orderPos + I * 8) x = c5 at dc5 assignRun
  rw [evaluate_delAssign c5 (ofString "i") (ofString "j") J I dc5.jL dc5.iL] at assignRun
  cases assignRun
  have dc6 := dc5.setI J jIn
  exact dc6.congr (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) pa pb pc
    (fun k member => plocals k (by intro h; subst h; revert member; decide))

#print axioms htabDelMove_normal

def delMoveCost (keyLength : BitVec 64) : Nat := keyLength.toNat / 32 + keyLength.toNat / 8 + 11

/-- The move block spends at most the copy bound in every outcome. -/
theorem runBounded_htabDelMove {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (budget : delMoveCost keyLength ≤ s.clock) :
    RunBounded s htabDelMove (delMoveCost keyLength) := by
  have inv := d.inv
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have strideLe : stride.toNat ≤ capacity.toNat * stride.toNat := Nat.le_mul_of_pos_left _ capPos
  have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have fits := inv.fits
  have small : keyLength.toNat ≤ 33806089496 := by omega
  have copyArgs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] =
        some [.val (.word (keys + I * stride)),.val (.word (keys + J * stride)),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,d.keysL,d.iL,d.jL,d.strideL,d.klenL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have copy : RunBounded s (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")]) (delMoveCost keyLength) :=
    evaluate_memcpy_call_bounded s _ _ _ keyLength copyArgs inv.code small budget
  rw [htabDelMove_shape]
  refine (RunBounded.seq copy (b := 0) (by omega) ?_).weaken (by omega)
  intro next _ nextCode _
  exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans inv.code) (Nat.zero_le _)

theorem htabDelMovable_avoids : ∀ k ∈ delLocalNames, avoidsLocal k htabDelMovable = true := by decide

/-- The read-only movability test keeps the backward-shift state. -/
theorem htabDelMovable_normal {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (run : evaluateHOLFiniteState s htabDelMovable = (none,post)) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I J := by
  have memory := (memoryFrame_leaf _ htabDelMovable_readOnly s d.inv.code).1
  have meta' := evaluateHOLFiniteState_metadata s htabDelMovable
  rw [run] at memory meta'
  exact d.congr (fun _ _ => by rw [memory]) (fun _ _ => by rw [memory]) (fun _ _ => by rw [memory])
    meta'.2.1 meta'.2.2.1 meta'.1 (fun k member => by
      have kept := evaluate_avoidsLocal_flowing k htabDelMovable (htabDelMovable_avoids k member) s
        (by rw [run]; exact Or.inl rfl)
      rw [run] at kept
      exact kept)

#print axioms runBounded_htabDelMove
#print axioms htabDelMovable_normal

theorem DelState.ofDec {F : Type} {inner post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ inner I J)
    {name : MlS} (fresh : name ∉ delLocalNames)
    (pm : post.memory = inner.memory) (pa : post.memaddrs = inner.memaddrs) (pb : post.be = inner.be)
    (pc : post.code = inner.code) (plocals : ∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I J :=
  d.congr (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) pa pb pc
    (fun k member => plocals k (fun h => fresh (h ▸ member)))

def htabDelCont : ProgHOL 64 :=
  .dec (ofString "home") .one (.op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]])
    (.dec (ofString "movable") .one (.const 0)
      (.seq htabDelMovable
        (.ite (.cmp .notEqual (.var .local (ofString "movable")) (.const 0)) htabDelMove .skip)))

/-- After the home hash: the movability test and optional move, bounded in
every outcome, keep the state normally with the hole at J or unchanged. -/
theorem htabDelCont_run {F : Type} {r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ r I J)
    (occupied : occ J ≠ some 0) (budget : delMoveCost keyLength ≤ r.clock) :
    RunBounded r htabDelCont (delMoveCost keyLength) ∧
      ∀ post, evaluateHOLFiniteState r htabDelCont = (none,post) →
        ∃ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I' J := by
  have code := d.inv.code
  constructor
  · apply RunBounded.dec
    intro v _
    apply RunBounded.dec
    intro v2 _
    have d2 := (d.setOther (ofString "home") v (by decide)).setOther (ofString "movable") v2 (by decide)
    refine (RunBounded.seq (a := 0) (RunBounded.ofProg (ProgBounded.straight _ htabDelMovable_straight) d2.inv.code
      (Nat.zero_le _)) (by simp [setVarHOLFinite]; omega) ?_).weaken (by omega)
    intro next run _ nb
    have dn := htabDelMovable_normal d2 run
    apply RunBounded.ite_cases
    · exact runBounded_htabDelMove dn nb
    · exact (RunBounded.ofProg (ProgBounded.straight _ (by decide)) dn.inv.code (Nat.zero_le _)).weaken (by omega)
  · intro post run
    obtain ⟨v,inner,_,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state run
    obtain ⟨v2,inner2,_,innerRun2,pm2,pa2,pb2,pc2,_,plocals2,_⟩ := dec_normal_state innerRun
    obtain ⟨mid,movRun,iteRun⟩ := seq_normal_parts innerRun2
    have d2 := (d.setOther (ofString "home") v (by decide)).setOther (ofString "movable") v2 (by decide)
    have dm := htabDelMovable_normal d2 movRun
    have clockKept := (RunBounded.ofProg (state := setVarHOLFinite (ofString "movable") v2 (setVarHOLFinite (ofString "home") v r))
      (ProgBounded.straight _ htabDelMovable_straight) d2.inv.code (Nat.zero_le _)).1
    rw [movRun] at clockKept
    simp only [setVarHOLFinite] at clockKept
    have finish : ∀ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ inner2 I' J →
        ∃ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I' J :=
      fun I' di => ⟨I',(di.ofDec (by decide) pm2 pa2 pb2 pc2 plocals2).ofDec (by decide) pm pa pb pc plocals⟩
    rcases ite_normal_cases mid inner2 _ _ _ iteRun with moved | skipped
    · exact finish J (htabDelMove_normal dm (by rw [dm.bytes J dm.jInside]; exact occupied) (by unfold delMoveCost at budget; omega) moved)
    · rw [evaluateHOLFiniteState_skip] at skipped
      cases skipped
      exact finish I dm

#print axioms htabDelCont_run
theorem delResVar_lookup_ne {β : Type} (m : HolFiniteMapExact MlS β) (key k : MlS) (opt : Option β)
    (ne : k ≠ key) : (HolFiniteMapExact.resVarEq m (key, opt)).lookup k = m.lookup k := by
  cases opt with
  | none => simp [FDOMSUB_HOL, ne]
  | some v => simp [FUPDATE_HOL, ne]

theorem decCall_normal_body {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (none,post)) :
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
      evaluateHOLFiniteState resumed continuation = (none,inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      (∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) := by
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
              ?pm,?pa,?pb,?pc,?pl⟩
            case m => rfl
            case a => rfl
            case b => rfl
            case c => rfl
            case pm => rw [← p]
            case pa => rw [← p]
            case pb => rw [← p]
            case pc => rw [← p]
            case pl =>
              intro k ne
              rw [← p]
              exact delResVar_lookup_ne _ _ _ _ ne
            case k =>
              intro le
              change (if _ then _ else _) = _
              rw [if_neg (by omega)]
            case n => simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            case l =>
              intro k ne
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
          · simp at run

#print axioms decCall_normal_body

theorem DelState.setJ {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J)
    (J' : BitVec 64) (inside : J'.toNat < capacity.toNat) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
      (setVarHOLFinite (ofString "j") (.val (.word J')) s) I J' := by
  have keep : ∀ k, k ≠ ofString "j" → (setVarHOLFinite (ofString "j") (.val (.word J')) s).locals.lookup k = s.locals.lookup k := by
    intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  exact { d with
    inv := { d.inv with }
    capL := (keep _ (by decide)).trans d.capL, usedL := (keep _ (by decide)).trans d.usedL,
    keysL := (keep _ (by decide)).trans d.keysL, strideL := (keep _ (by decide)).trans d.strideL,
    klenL := (keep _ (by decide)).trans d.klenL, valsL := (keep _ (by decide)).trans d.valsL,
    orderL := (keep _ (by decide)).trans d.orderL, orderPosL := (keep _ (by decide)).trans d.orderPosL,
    iL := (keep _ (by decide)).trans d.iL,
    jL := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE], jInside := inside }

theorem DelState.clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J) :
    DelState keyLength table keys stride capacity used values order orderPos count empty bits occ (decClockHOLFinite s) I J :=
  d.congr (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl (fun _ _ => rfl)

theorem eval_delLoadByte {F : Type} (s : PanSemStateFiniteExact 64 F) (used J : BitVec 64) (byte : UInt8)
    (usedL : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (jL : s.locals.lookup (ofString "j") = some (.val (.word J)))
    (loaded : hashOccupancyRead s used J = some byte) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) =
        some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  unfold hashOccupancyRead at loaded
  simp [evalHOLExact,evalListHOLExact,usedL,jL,wordOpHOL,wordOp,valueIsWord,valueWord,loaded]

theorem evaluate_delBreakCheck_none {F : Type} (s : PanSemStateFiniteExact 64 F) (used J : BitVec 64) (yes no : ProgHOL 64)
    (usedL : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (jL : s.locals.lookup (ofString "j") = some (.val (.word J)))
    (loaded : hashOccupancyRead s used J = none) :
    evaluateHOLFiniteState s (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")]))
      (.const 0)) yes no) = (some .error,s) := by
  unfold hashOccupancyRead at loaded
  rw [evaluateHOLFiniteState_ite]
  simp [evalHOLFinite_eq_toExact,evalHOLExact,evalListHOLExact,usedL,jL,wordOpHOL,wordOp,valueIsWord,valueWord,loaded]

#print axioms evaluate_delBreakCheck_none

def delIterCost (keyLength : BitVec 64) : Nat := keyLength.toNat / 8 + 8 + 1 + delMoveCost keyLength

theorem htabDelBody_cont_shape : htabDelBody =
    .seq (hashProbeStep (ofString "j"))
      (.seq (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip)
        (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")] htabDelCont)) := rfl

/-- The home-hash call and continuation from a state whose probe slot J is occupied. -/
theorem htabDelHash_run {F : Type} {r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ r I J)
    (occupied : occ J ≠ some 0) (budget : delIterCost keyLength ≤ r.clock) :
    let call : ProgHOL 64 := .decCall (ofString "h") .one (ofString "htab_hash")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] htabDelCont
    RunBounded r call (delIterCost keyLength) ∧
      ∀ post, evaluateHOLFiniteState r call = (none,post) →
        ∃ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I' J := by
  intro call
  have inv := d.inv
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have strideLe : stride.toNat ≤ capacity.toNat * stride.toNat := Nat.le_mul_of_pos_left _ capPos
  have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have fits := inv.fits
  have small : keyLength.toNat < 2 ^ 62 := by omega
  have args : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a))
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] = some [.val (.word (keys + J * stride)),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,d.keysL,d.jL,d.strideL,d.klenL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  -- the resumed state after any returned hash run
  have resume : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F), post.code = r.code → post.memory = r.memory →
      post.memaddrs = r.memaddrs → post.be = r.be →
      DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
        (setVarHOLFinite (ofString "h") value {post with locals := r.locals}) I J := by
    intro value post c m a b
    have d' : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ
        {post with locals := r.locals} I J :=
      d.congr (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) a b c (fun _ _ => rfl)
    exact d'.setOther _ _ (by decide)
  constructor
  · unfold delIterCost at budget ⊢
    refine runBounded_htabHash_decCall r (ofString "h") _ _ htabDelCont (keys + J * stride) keyLength inv.code args small
      budget ?_
    intro value post c m a b _ tc
    exact (htabDelCont_run (resume value post c m a b) occupied tc).1
  · intro post run
    obtain ⟨values,body,callee,returnShape,w,bodyPost,resumed,inner,args',lookup,bodyRun,rm,ra,rb,rc,rclk,_,rlocals,
      contRun,pm,pa,pb,pc,pl⟩ := decCall_normal_body run
    rw [args] at args'
    cases args'
    have installed : r.code.lookup (ofString "htab_hash") =
        some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
      rw [inv.code]; exact originalRuntimeCode_hash_lookup
    rw [pan_two_word_lookup r.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
      (sourceFunctionBody Guest.guestFn_htab_hash) (keys + J * stride) keyLength (by decide) installed] at lookup
    cases lookup
    have entryBound := evaluate_htabHash_body_bounded (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
      (by exact inv.code) keyLength (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small
      (by change _ ≤ r.clock - 1; unfold delIterCost at budget; omega)
    have memory := evaluate_readOnly_memory _ htabHash_readOnly (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
      (sourceFunctionBody Guest.guestFn_htab_hash)
    unfold RunBounded at entryBound
    rw [bodyRun] at memory meta' entryBound
    obtain ⟨spent,kept,_⟩ := entryBound
    have resumedClock := rclk kept
    have dr : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ resumed I J :=
      d.congr (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl)
        (ra.trans meta'.2.1) (rb.trans meta'.2.2.1) (rc.trans meta'.1)
        (fun k member => rlocals k (fun h => by subst h; revert member; decide))
    obtain ⟨I',di⟩ := (htabDelCont_run dr occupied (by
      change r.clock - 1 ≤ bodyPost.clock + _ at spent
      unfold delIterCost at budget; omega)).2 inner contRun
    exact ⟨I',di.congr (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) pa pb pc
      (fun k member => pl k (fun h => by subst h; revert member; decide))⟩

#print axioms htabDelHash_run

theorem byte_word_ne_zero (byte : UInt8) (b : byte ≠ 0) : (BitVec.ofNat 64 byte.toNat) ≠ 0 := by
  intro h
  apply b
  have h2 : byte.toNat = 0 := by
    have := congrArg BitVec.toNat h
    have small : byte.toNat < 2 ^ 64 := by have := byte.toNat_lt; omega
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using this
  exact UInt8.toNat_inj.mp h2

/-- One backward-shift iteration: bounded in every outcome; a normal outcome
advanced J to an occupied slot, a break saw the next slot empty. -/
theorem htabDelBody_run {F : Type} {t : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I J : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ t I J)
    (budget : delIterCost keyLength ≤ t.clock) :
    RunBounded t htabDelBody (delIterCost keyLength) ∧
      (∀ post, evaluateHOLFiniteState t htabDelBody = (none,post) → occ (hashProbeNext J capacity) ≠ some 0 ∧
        ∃ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I'
          (hashProbeNext J capacity)) ∧
      (∀ post, evaluateHOLFiniteState t htabDelBody = (some .break,post) → occ (hashProbeNext J capacity) = some 0 ∧
        ∃ I', DelState keyLength table keys stride capacity used values order orderPos count empty bits occ post I'
          (hashProbeNext J capacity)) := by
  have inv := d.inv
  have nextInside : (hashProbeNext J capacity).toNat < capacity.toNat := by
    rw [hashProbeNext_toNat J capacity bits inv.power d.jInside]
    exact Nat.mod_lt _ (by rw [inv.power]; exact Nat.two_pow_pos bits)
  have d1 := d.setJ _ nextInside
  rw [htabDelBody_cont_shape]
  have whole := evaluateHOLFiniteState_seq_line780 t (hashProbeStep (ofString "j"))
    (.seq (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip)
        (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")] htabDelCont))
  rw [evaluate_hashProbeStep t (ofString "j") J capacity d.jL d.capL] at whole
  dsimp only at whole
  have clk : (setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext J capacity))) t).clock = t.clock := rfl
  generalize setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext J capacity))) t = t1 at d1 whole clk
  unfold RunBounded
  rw [whole]
  have restSeq := fun (x : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) (h : evaluateHOLFiniteState t1
      (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip) = x) => (evaluateHOLFiniteState_seq_line780 t1 _ (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")] htabDelCont)).trans (by rw [h])
  have read := d1.bytes _ nextInside
  cases hb : occ (hashProbeNext J capacity) with
  | none =>
    rw [hb] at read
    have rest := restSeq _ (evaluate_delBreakCheck_none t1 used _ .break .skip d1.usedL d1.jL read)
    dsimp only at rest
    rw [rest]
    dsimp only
    refine ⟨⟨by omega,by omega,by simp⟩,fun post h => by simp at h,fun post h => by simp at h⟩
  | some b =>
    rw [hb] at read
    have ite := evaluate_loaded_word_ite t1 _ (BitVec.ofNat 64 b.toNat) 0 .equal
      (eval_delLoadByte t1 used _ b d1.usedL d1.jL read) .break .skip
    by_cases zero : b = 0
    · subst zero
      have iteB : evaluateHOLFiniteState t1
          (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
            .break .skip) = (some .break,t1) := by
        rw [ite]; simp [Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_break]
      have rest := restSeq _ iteB
      dsimp only at rest
      rw [rest]
      dsimp only
      refine ⟨⟨by omega,by omega,by simp⟩,fun post h => by simp at h,fun post h => ?_⟩
      simp only [Prod.mk.injEq,true_and] at h
      subst h
      exact ⟨rfl,I,d1⟩
    · have iteS : evaluateHOLFiniteState t1
          (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
            .break .skip) = (none,t1) := by
        rw [ite]; simp [Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]; exact byte_word_ne_zero b zero
      have rest := restSeq _ iteS
      dsimp only at rest
      rw [rest]
      have occupied : occ (hashProbeNext J capacity) ≠ some 0 := by
        rw [hb]; intro h; exact zero (Option.some.inj h)
      obtain ⟨bounded,normal⟩ := htabDelHash_run d1 occupied (by omega)
      unfold RunBounded at bounded
      refine ⟨⟨by omega,by omega,bounded.2.2⟩,fun post h => ⟨fun e => zero (Option.some.inj e),normal post h⟩,fun post h => ?_⟩
      exact absurd (congrArg Prod.fst h) (evaluate_noTopBreak _ (by decide) t1)

#print axioms htabDelBody_run

/-- Loop rank: occupied probe slots are within cyclic distance of the empty
slot; an empty probe slot (only after a break) has rank above capacity. -/
def DelRank (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64) (bits : Nat)
    (occ : BitVec 64 → Option UInt8) {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ I J, DelState keyLength table keys stride capacity used values order orderPos count empty bits occ s I J ∧
    (occ J ≠ some 0 → hashProbeDistance capacity.toNat J.toNat empty.toNat < n) ∧
    (occ J = some 0 → capacity.toNat < n)

/-- The backward-shift loop from rank n runs within n * (iteration + 1) ticks in every outcome. -/
theorem htabDelLoop_run (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64) (bits : Nat)
    (occ : BitVec 64 → Option UInt8) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      DelRank keyLength table keys stride capacity used values order orderPos count empty bits occ state n →
      n * (delIterCost keyLength + 1) ≤ state.clock →
      RankedOutcome state (.const 1) (n * (delIterCost keyLength + 1))
        (DelRank keyLength table keys stride capacity used values order orderPos count empty bits occ) True
        (evaluateHOLFiniteState state (.while (.const 1) htabDelBody)) := by
  refine rankedWhile_run (.const 1) htabDelBody (delIterCost keyLength)
    (DelRank keyLength table keys stride capacity used values order orderPos count empty bits occ) True ?_ ?_
  · intro F s ranked w _
    obtain ⟨I,J,_,a,b⟩ := ranked
    by_cases h : occ J = some 0
    · exact absurd (b h) (by omega)
    · exact absurd (a h) (by omega)
  · intro F s n w code ranked _ _ budget
    obtain ⟨I,J,d,a,b⟩ := ranked
    have inv := d.inv
    obtain ⟨bounded,normal,broken⟩ := htabDelBody_run d.clock (by change _ ≤ s.clock - 1; omega)
    unfold RunBounded at bounded
    obtain ⟨spent,kept,safe⟩ := bounded
    have nextInside : (hashProbeNext J capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat J capacity bits inv.power d.jInside]
      exact Nat.mod_lt _ (by rw [inv.power]; exact Nat.two_pow_pos bits)
    have farNext := hashProbeDistance_lt_capacity capacity.toNat (hashProbeNext J capacity).toNat empty.toNat nextInside
      d.emptyInside
    refine ⟨spent,kept,safe,?_,?_⟩
    · intro flow
      rcases flow with flow | flow
      · obtain ⟨occupied,I',d'⟩ := normal _ (Prod.ext flow rfl)
        refine ⟨n,le_refl _,⟨I',hashProbeNext J capacity,d',fun _ => ?_,fun h => absurd h occupied⟩,d'.inv.code.trans code.symm⟩
        by_cases here : occ J = some 0
        · have := b here; omega
        · have far := a here
          have differs : J.toNat ≠ empty.toNat := by
            intro same
            have equal : J = empty := BitVec.eq_of_toNat_eq same
            exact here (equal ▸ d.emptyByte)
          have decreased := hashProbeDistance_decreases capacity.toNat J.toNat empty.toNat d.jInside d.emptyInside differs
          rw [← hashProbeNext_wrap J capacity bits inv.power d.jInside] at decreased
          omega
      · exact absurd flow (evaluate_noTopContinue _ (by decide) _)
    · intro flow
      obtain ⟨_,I',d'⟩ := broken _ (Prod.ext flow rfl)
      exact ⟨trivial,capacity.toNat + 1,⟨I',hashProbeNext J capacity,d',fun _ => by omega,fun _ => by omega⟩,
        d'.inv.code.trans code.symm⟩

#print axioms htabDelLoop_run

theorem htabDelTail_straight : extStraightLine htabDelTail = true := by decide

theorem htabDelMissing_normal {F : Type} (s next : PanSemStateFiniteExact 64 F) (I C : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (capL : s.locals.lookup (ofString "cap") = some (.val (.word C)))
    (run : evaluateHOLFiniteState s htabDelMissing = (none,next)) : next = s ∧ I ≠ C := by
  unfold htabDelMissing at run
  rw [evaluateHOLFiniteState_ite] at run
  by_cases same : I = C
  · subst same
    simp [evalHOLFinite_eq_toExact,evalHOLExact,iL,capL,Compiler.Encoders.Asm.wordCmpHOL,
      evaluateHOLFiniteState_return,shapeOfHOLExact] at run
  · simp [evalHOLFinite_eq_toExact,evalHOLExact,iL,capL,Compiler.Encoders.Asm.wordCmpHOL,same,
      evaluateHOLFiniteState_skip] at run
    exact ⟨run.symm,same⟩

#print axioms htabDelMissing_normal

def htabDelAfterFind : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_htab_del with
  | .decCall _ _ _ _ rest => rest
  | _ => .skip

def htabDelHeaders : ProgHOL 64 :=
  match htabDelAfterFind with
  | .dec _ _ _ (.seq _ rest) => rest
  | _ => .skip

theorem htabDelAfterFind_shape : htabDelAfterFind =
    .dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) (.seq htabDelMissing htabDelHeaders) := by
  unfold htabDelHeaders htabDelAfterFind; rw [source_htabDel_body]; rfl

theorem htabDelHeaders_shape : htabDelHeaders =
    (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0))
    (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8))
    (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32))
    (.dec (ofString "vals") .one (.load .one (hashLocalAddress (ofString "t") 40))
    (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48))
    (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56))
    (.dec (ofString "order_pos") .one (.load .one (hashLocalAddress (ofString "t") 64))
    (.dec (ofString "deleted_pos") .one (.load .one (.op .add [.var .local (ofString "order_pos"),
        .panop .mul [.var .local (ofString "i"),.const 8]]))
    (.dec (ofString "j") .one (.var .local (ofString "i"))
    (.seq (.while (.const 1) htabDelBody) htabDelTail)))))))))) := by
  unfold htabDelHeaders htabDelAfterFind; rw [source_htabDel_body]; rfl

def delLoopCost (keyLength capacity : BitVec 64) : Nat := (capacity.toNat + 1) * (delIterCost keyLength + 1)

/-- The backward-shift loop and the straight tail from the loop-entry state. -/
theorem runBounded_htabDelLoopTail {F : Type} {X : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {I : BitVec 64}
    (d : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ X I I)
    (budget : delLoopCost keyLength capacity + 0 ≤ X.clock) :
    RunBounded X (.seq (.while (.const 1) htabDelBody) htabDelTail) (delLoopCost keyLength capacity + 0) := by
  have far := hashProbeDistance_lt_capacity capacity.toNat I.toNat empty.toNat d.iInside d.emptyInside
  have loop := htabDelLoop_run keyLength table keys stride capacity used values order orderPos count empty bits occ
    (capacity.toNat + 1) X d.inv.code ⟨I,I,d,fun _ => by omega,fun _ => by omega⟩ (by unfold delLoopCost at budget; omega)
  refine RunBounded.seq ⟨loop.1,loop.2.1,loop.2.2.1⟩ budget ?_
  intro next _ nextCode _
  exact RunBounded.ofProg (ProgBounded.straight _ htabDelTail_straight) (nextCode.trans d.inv.code) (Nat.zero_le _)

#print axioms runBounded_htabDelLoopTail


/-- After lookup returned a slot I ≤ cap: the missing-key exit, header loads,
the backward-shift loop and the straight tail. -/
theorem runBounded_htabDelAfterFind {F : Type} (r : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count I : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits r)
    (tableLocal : r.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : r.locals.lookup (ofString "i") = some (.val (.word I))) (indexLe : I.toNat ≤ capacity.toNat)
    (room : count.toNat < capacity.toNat) (positions : OrderPosBounded r capacity used orderPos)
    (budget : 0 + (delLoopCost keyLength capacity + 0) ≤ r.clock) :
    RunBounded r htabDelAfterFind (0 + (delLoopCost keyLength capacity + 0)) := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead r used)
    (by rw [← inv.agreement]; exact room)
  rw [htabDelAfterFind_shape]
  apply runBounded_header_load r _ _ table 16 capacity _ tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16
  refine RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ (by decide)) inv.code (Nat.zero_le _)) (by
    simp only [setVarHOLFinite]; omega) ?_
  intro next missing _ _
  obtain ⟨rfl,differs⟩ := htabDelMissing_normal _ next I capacity
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal])
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) missing
  have inside : I.toNat < capacity.toNat := by
    have : I.toNat ≠ capacity.toNat := fun h => differs (BitVec.eq_of_toNat_eq h)
    omega
  rw [htabDelHeaders_shape]
  apply runBounded_header_load _ _ _ table 0 keyLength _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 0 (by omega) (by omega)) (by exact inv.cell0)
  apply runBounded_header_load _ _ _ table 8 stride _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)
  apply runBounded_header_load _ _ _ table 32 keys _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 32 (by omega) (by omega)) (by exact inv.cell32)
  apply runBounded_header_load _ _ _ table 40 values _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 40 (by omega) (by omega)) (by exact inv.cell40)
  apply runBounded_header_load _ _ _ table 48 used _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 48 (by omega) (by omega)) (by exact inv.cell48)
  apply runBounded_header_load _ _ _ table 56 order _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 56 (by omega) (by omega)) (by exact inv.cell56)
  apply runBounded_header_load _ _ _ table 64 orderPos _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 64 (by omega) (by omega)) (by exact inv.cell64)
  apply RunBounded.dec
  intro deleted _
  apply RunBounded.decWord _ _ _ I (eval_delVar _ _ I
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal]))
  refine runBounded_htabDelLoopTail (occ := fun q => hashOccupancyRead r used q) (empty := empty) (count := count) (bits := bits)
    (table := table) (keys := keys) (stride := stride) (used := used) (values := values) (order := order)
    (orderPos := orderPos) (I := I) ?_ (by simp only [setVarHOLFinite]; omega)
  exact {
    inv := inv.transfer rfl rfl rfl rfl
    bytes := fun q _ => rfl
    emptyByte := emptyRead
    orderPosOK := positions
    capL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    usedL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    keysL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    strideL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    klenL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    valsL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    orderL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    orderPosL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    iL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal]
    jL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    iInside := inside
    emptyInside := emptyInside
    jInside := inside }

#print axioms runBounded_htabDelAfterFind

theorem source_htabDel_afterFind : sourceFunctionBody Guest.guestFn_htab_del =
    .decCall (ofString "i") .one (ofString "htab_find_slot") [.var .local (ofString "t"),.var .local (ofString "key")]
      htabDelAfterFind := by
  unfold htabDelAfterFind
  generalize hb : sourceFunctionBody Guest.guestFn_htab_del = b
  rw [source_htabDel_body] at hb
  subst hb
  rfl

theorem OrderPosBounded.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {capacity used orderPos : BitVec 64} (positions : OrderPosBounded s capacity used orderPos)
    (memory : r.memory = s.memory) (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) :
    OrderPosBounded r capacity used orderPos := by
  intro q inside occupied
  have read : hashOccupancyRead r used q = hashOccupancyRead s used q := by
    unfold hashOccupancyRead; rw [memory,addresses,endian]
  rw [memory]
  exact positions q inside (by rw [← read]; exact occupied)

/-- Cost of the original del body: lookup, then at most capacity + 1
backward-shift iterations (home hash plus one key copy each); the missing-key
exit, header loads and the order-list tail are straight-line. -/
def delBodyCost (keyLength capacity : BitVec 64) : Nat :=
  keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0) + 1 +
    (0 + (delLoopCost keyLength capacity + 0))

/-- The original `htab_del` body on an aligned table with count < capacity and
in-table order positions for occupied slots spends at most delBodyCost ticks in
every outcome. -/
theorem evaluate_htabDel_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (room : count.toNat < capacity.toNat) (positions : OrderPosBounded state capacity used orderPos)
    (small : keyLength.toNat ≤ 33806089496)
    (budget : delBodyCost keyLength capacity ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_del) (delBodyCost keyLength capacity) := by
  unfold delBodyCost at budget ⊢
  rw [source_htabDel_afterFind]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  have entryT : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  constructor
  · exact evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used empty bits
      entryT (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
      entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
      (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
      entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
      (by rw [entryFacts.2.2.2.2.2]; omega)
  · intro v post run tc
    obtain ⟨I,rfl,indexLe⟩ := htabFindSlot_returned_range entry post table capacity bits inv.power entryT
      (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 v run
    have frame := htabFindSlot_memoryFrame entry entryInv.code
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
    rw [run] at frame meta'
    generalize hr : setVarHOLFinite (ofString "i") (.val (.word I)) { post with locals := state.locals } = r
    have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
        r.clock = post.clock := by
      rw [← hr]
      exact ⟨frame.1.trans entryFacts.1,meta'.2.1.trans entryFacts.2.1,meta'.2.2.1.trans entryFacts.2.2.1,
        meta'.1.trans entryFacts.2.2.2.1,rfl⟩
    have rLocal : ∀ k, k ≠ ofString "i" → r.locals.lookup k = state.locals.lookup k := by
      intro k ne; rw [← hr]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    have rI : r.locals.lookup (ofString "i") = some (.val (.word I)) := by
      rw [← hr]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    exact runBounded_htabDelAfterFind r keyLength table keys stride capacity used values order orderPos count I bits
      (inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1) ((rLocal _ (by decide)).trans tableLocal) rI indexLe
      room (positions.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1) (by rw [rFacts.2.2.2.2]; exact tc)

#print axioms evaluate_htabDel_body_bounded

/-- A handler-free `htab_del` call on word arguments costs delBodyCost + 1 in every outcome. -/
theorem runBounded_htabDel_call {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (tableArgument keyArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (room : count.toNat < capacity.toNat) (positions : OrderPosBounded state capacity used orderPos)
    (small : keyLength.toNat ≤ 33806089496)
    (budget : delBodyCost keyLength capacity + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_del") [tableArgument,keyArgument])
      (delBodyCost keyLength capacity + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_del") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_del) table key (by decide)
    (by rw [inv.code]; exact originalRuntimeCode_hashDelete_lookup)] at lookup
  cases lookup
  exact evaluate_htabDel_body_bounded _ keyLength table keys stride capacity used values order orderPos count key bits
    (inv.transfer rfl rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    room (positions.transfer rfl rfl rfl) small (by change _ ≤ state.clock - 1; omega)

#print axioms runBounded_htabDel_call
end InitECandidate.Runtime
