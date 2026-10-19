import InitECandidate.Runtime.HtabSetLaid
import InitECandidate.Runtime.OriginalHashUnionCode
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! `htab_union_into(dst, src)` on actual layouts: the destination is an aligned heap table or a
descending scratch table (`HtabLaid`), the source is any table whose read words (header cells
8/32/40/56, order entries below its count, and the value words they select) are mapped, hold words
and lie below the entry heap pointer outside the destination header and array block. The loop
inserts through `htab_set` (growing tables move their arrays to fresh heap memory), and every
word below the entry heap pointer outside the destination's header and initial block is kept. -/

/-- A tail call to an installed body that keeps memory and globals keeps them too. -/
theorem memoryFrame_tailCall (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : MemoryFrame body) : MemoryFrame (.call none function arguments) := by
  intro F state code
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; exact ⟨rfl,rfl⟩
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; exact ⟨rfl,rfl⟩
    | some found =>
      obtain ⟨foundBody,callee,foundShape⟩ := found
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body foundBody returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      exact evaluate_tailCall_body_frame state function arguments values foundBody callee foundShape args lookup
        (bodyFrame _ (by exact code))

theorem htabItem_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_item) := by
  rw [source_htabItem_body]
  exact memoryFrame_dec _ _ _ (memoryFrame_tailCall _ _ _ _ _ vmLookup_htab_slot htabSlot_memoryFrame)

#print axioms htabItem_memoryFrame

/-- A normally finishing declared call, with the callee and continuation globals. -/
theorem decCall_normal_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (none,post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (returnShape : ShapeHOL) (w : ValueHOL 64) (bodyPost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w),bodyPost) ∧
      resumed.memory = bodyPost.memory ∧ resumed.memaddrs = bodyPost.memaddrs ∧ resumed.be = bodyPost.be ∧
      resumed.code = bodyPost.code ∧ resumed.globals = bodyPost.globals ∧
      (bodyPost.clock ≤ (callEntryStateHOLFinite s callee).clock → resumed.clock = bodyPost.clock) ∧
      resumed.locals.lookup name = some w ∧
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧
      evaluateHOLFiniteState resumed continuation = (none,inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      post.globals = inner.globals ∧ (∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) := by
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
            refine ⟨values,body,callee,returnShape,w,bodyPost,_,_,rfl,lookup,bodyRun,?m,?a,?b,?c,?g,?k,?n,?l,Prod.ext e rfl,
              ?pm,?pa,?pb,?pc,?pg,?pl⟩
            case m => rfl
            case a => rfl
            case b => rfl
            case c => rfl
            case g => rfl
            case pg => rw [← p]
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

#print axioms decCall_normal_globals

theorem source_htabUnionInto_body : sourceFunctionBody Guest.guestFn_htab_union_into =
    .dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "src"),.const 24]))
      (.dec (ofString "i") .one (.const 0)
        (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
          (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
            [.var .local (ofString "src"),.var .local (ofString "i")]
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none,none)) (ofString "htab_set")
                  [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))))
          (.return (.const 0)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem setBodyCost_mono (keyLength a b n m : BitVec 64) (ab : a.toNat ≤ b.toNat) (nm : n.toNat ≤ m.toNat)
    (fits : b.toNat * 2 < 2 ^ 64) : setBodyCost keyLength a n ≤ setBodyCost keyLength b m := by
  have a2 : (a * 2).toNat = a.toNat * 2 := BitVec.toNat_mul_of_lt (by change a.toNat * 2 < 2 ^ 64; omega)
  have b2 : (b * 2).toNat = b.toNat * 2 := BitVec.toNat_mul_of_lt (by change b.toNat * 2 < 2 ^ 64; omega)
  have i := insertCallCost_mono keyLength (a * 2) (b * 2) (by omega)
  have m1 : a.toNat * (4 * keyLength.toNat + 1 + 0 + 1) ≤ b.toNat * (4 * keyLength.toNat + 1 + 0 + 1) :=
    Nat.mul_le_mul_right _ ab
  have m2 : n.toNat * (insertCallCost keyLength (a * 2) + 1) ≤ m.toNat * (insertCallCost keyLength (b * 2) + 1) :=
    Nat.mul_le_mul nm (by omega)
  unfold setBodyCost growBodyCost
  omega

theorem runBounded_htabSet_call_laid {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
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
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])
      (setBodyCost keyLength capacity count + 1) := by
  rcases laid with ⟨inv,_,_⟩ | ⟨inv,_,_⟩
  · exact runBounded_htabSet_call state destination _ _ _ keyLength table keys stride capacity used values order orderPos
      count key value pointer bits inv args heap pointerAligned headerBelow pointerInside arena room small budget
  · exact runBounded_htabSet_call_desc state destination _ _ _ keyLength table keys stride capacity used values order orderPos
      count key value pointer bits inv args heap pointerAligned headerBelow pointerInside arena room small budget

/-- A conditional whose condition evaluates to a word is bounded by the bound of the taken branch. -/
theorem RunBounded.iteWord {F : Type} (state : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64)
    {yes no : ProgHOL 64} {cost : Nat} (w : BitVec 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) condition =
      some (.val (.word w)))
    (taken : w ≠ 0 → RunBounded state yes cost) (skipped : w = 0 → RunBounded state no cost) :
    RunBounded state (.ite condition yes no) cost := by
  unfold RunBounded at taken skipped ⊢
  rw [evaluateHOLFiniteState_ite,evaluated]
  dsimp only
  by_cases zero : w = 0
  · rw [if_pos zero]; exact skipped zero
  · rw [if_neg zero]; exact taken zero


def unionSetIte : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
    (.call (some (none,none)) (ofString "htab_set")
      [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
    .skip

def unionIncr : ProgHOL 64 := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])

def unionIter : ProgHOL 64 :=
  .decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
    [.var .local (ofString "src"),.var .local (ofString "i")] (.seq unionSetIte unionIncr)

def unionCond : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))

/-- The fixed data of one `htab_union_into` run: the destination table's key length, header and
stride, its initial count/capacity and array block [lo0, hi0), the source header words, the heap
pointer at entry, and the entry memory, address set and globals. -/
structure UnionCtx where
  keyLength : BitVec 64
  dst : BitVec 64
  stride : BitVec 64
  src : BitVec 64
  n : BitVec 64
  skeys : BitVec 64
  sstride : BitVec 64
  svalues : BitVec 64
  sorder : BitVec 64
  count0 : BitVec 64
  capacity0 : BitVec 64
  pointer0 : BitVec 64
  lo0 : Nat
  hi0 : Nat
  M0 : BitVec 64 → HolWordLab 64
  A0 : BitVec 64 → Prop
  G0 : HolFiniteMapExact MlS (ValueHOL 64)

/-- Addresses below the entry heap pointer outside the destination header and initial block. -/
def UnionCtx.Away (c : UnionCtx) (w : BitVec 64) : Prop :=
  w.toNat < c.pointer0.toNat ∧ (w.toNat < c.dst.toNat ∨ c.dst.toNat + 72 ≤ w.toNat) ∧
    (w.toNat < c.lo0 ∨ c.hi0 ≤ w.toNat)

/-- Every word the source reads touch is mapped, holds a word and lies away from the destination. -/
def UnionCtx.SrcReads (c : UnionCtx) : Prop :=
  (c.A0 (c.src + 56) ∧ c.M0 (c.src + 56) = .word c.sorder ∧ c.Away (c.src + 56)) ∧
  (c.A0 (c.src + 32) ∧ c.M0 (c.src + 32) = .word c.skeys ∧ c.Away (c.src + 32)) ∧
  (c.A0 (c.src + 8) ∧ c.M0 (c.src + 8) = .word c.sstride ∧ c.Away (c.src + 8)) ∧
  (c.A0 (c.src + 40) ∧ c.M0 (c.src + 40) = .word c.svalues ∧ c.Away (c.src + 40)) ∧
  ∀ k : BitVec 64, k.toNat < c.n.toNat → ∃ slot vv : BitVec 64,
    c.A0 (c.sorder + k * 8) ∧ c.M0 (c.sorder + k * 8) = .word slot ∧ c.Away (c.sorder + k * 8) ∧
    c.A0 (c.svalues + slot * 8) ∧ c.M0 (c.svalues + slot * 8) = .word vv ∧ c.Away (c.svalues + slot * 8)

/-- Sizes and placement of the run. -/
def UnionCtx.Ok (c : UnionCtx) : Prop :=
  c.dst.toNat + 72 ≤ c.pointer0.toNat ∧ c.pointer0.toNat % 8 = 0 ∧ c.pointer0.toNat ≤ 33806089496 ∧
  (∀ a : BitVec 64, a.toNat % 8 = 0 → c.dst.toNat ≤ a.toNat → a.toNat < 33806089496 → c.A0 a) ∧
  c.keyLength.toNat ≤ 33806089496 ∧ c.capacity0.toNat ≤ 33806089496 ∧ c.n.toNat ≤ 33806089496 ∧
  c.count0.toNat < c.capacity0.toNat

def UnionCtx.capMax (c : UnionCtx) : Nat := max c.capacity0.toNat (4 * (c.count0.toNat + c.n.toNat))

/-- One iteration: the item call, its entry tick, and the set call with its tick. -/
def UnionCtx.stepCost (c : UnionCtx) : Nat :=
  1 + 1 + ((setBodyCost c.keyLength (BitVec.ofNat 64 c.capMax) (BitVec.ofNat 64 (c.count0.toNat + c.n.toNat)) + 1) + 0)

/-- The destination table during the loop, after `I` source items. -/
def UnionCtx.Dst (c : UnionCtx) (I : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (capacity keys used values order orderPos count : BitVec 64) (bits lo hi : Nat),
    HtabLaid c.keyLength c.dst keys c.stride capacity used values order orderPos count bits lo hi s ∧
    OrderInv s capacity count used order orderPos ∧ count.toNat < capacity.toNat ∧
    c.count0.toNat ≤ count.toNat ∧ count.toNat ≤ c.count0.toNat + I.toNat ∧
    (capacity.toNat ≤ c.capacity0.toNat ∨ capacity.toNat ≤ 4 * count.toNat) ∧
    ((lo = c.lo0 ∧ hi = c.hi0) ∨ c.pointer0.toNat ≤ lo)

def UnionCtx.Heap (c : UnionCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ c.pointer0.toNat ≤ p.toNat ∧
    p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496) ∧ HeapRel c.G0 s.globals

/-- Loop rank: counter I ≤ n with at most m items left, the loop locals, the source reads
unchanged, the destination table and the heap pointer. -/
def UnionRank (c : UnionCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) (m : Nat) : Prop :=
  ∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ c.n.toNat ∧
    c.n.toNat - I.toNat ≤ m ∧
    s.locals.lookup (ofString "cap") = some (.val (.word c.n)) ∧
    s.locals.lookup (ofString "dst") = some (.val (.word c.dst)) ∧
    s.locals.lookup (ofString "src") = some (.val (.word c.src)) ∧
    s.memaddrs = c.A0 ∧ (∀ w, c.Away w → s.memory w = c.M0 w) ∧ c.Dst I s ∧ c.Heap s

/-- The source item read of one iteration returns three words. -/
theorem union_item_returned (c : UnionCtx) (reads : c.SrcReads) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (I : BitVec 64) (lt : I.toNat < c.n.toNat) (code : s.code = originalRuntimeCode)
    (addrs : s.memaddrs = c.A0) (mem : ∀ w, c.Away w → s.memory w = c.M0 w) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (sourceFunctionBody Guest.guestFn_htab_item) = (some (.returned value),post)) :
    ∃ b kp vv : BitVec 64, value = .rStruct [.val (.word b),.val (.word kp),.val (.word vv)] := by
  obtain ⟨⟨a56,m56,w56⟩,⟨a32,m32,w32⟩,⟨a8,m8,w8⟩,⟨a40,m40,w40⟩,items⟩ := reads
  obtain ⟨slot,vv,aO,mO,wO,aV,mV,wV⟩ := items I lt
  obtain ⟨b,e⟩ := htabItem_returned (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
    post value c.src I c.sorder slot c.skeys c.sstride c.svalues vv (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change s.memaddrs _; rw [addrs]; exact a56) (by change s.memory _ = _; rw [mem _ w56]; exact m56)
    (by change s.memaddrs _; rw [addrs]; exact aO) (by change s.memory _ = _; rw [mem _ wO]; exact mO)
    (by change s.memaddrs _; rw [addrs]; exact a32) (by change s.memory _ = _; rw [mem _ w32]; exact m32)
    (by change s.memaddrs _; rw [addrs]; exact a8) (by change s.memory _ = _; rw [mem _ w8]; exact m8)
    (by change s.memaddrs _; rw [addrs]; exact a40) (by change s.memory _ = _; rw [mem _ w40]; exact m40)
    (by change s.memaddrs _; rw [addrs]; exact aV) (by change s.memory _ = _; rw [mem _ wV]; exact mV) run
  exact ⟨b,_,vv,e⟩

#print axioms union_item_returned

theorem union_guard_word {F : Type} (T : PanSemStateFiniteExact 64 F) (b kp vv : BitVec 64)
    (sL : T.locals.lookup (ofString "s") = some (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)])) :
    ∃ gw : BitVec 64, @evalHOLExact 64 F _ T.toExact (fun a => Classical.propDecidable (T.memaddrs a))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0)) = some (.val (.word gw)) := by
  simp [evalHOLExact,sL]

theorem union_set_args {F : Type} (T : PanSemStateFiniteExact 64 F) (dst b kp vv : BitVec 64)
    (dL : T.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (sL : T.locals.lookup (ofString "s") = some (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)])) :
    evalListHOLFinite T (h := fun a => Classical.propDecidable (T.memaddrs a))
      [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))] =
      some [.val (.word dst),.val (.word kp),.val (.word vv)] := by
  rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,dL,sL]

theorem ofNat_toNat_small (x : Nat) (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The current destination's set cost is below the iteration bound. -/
theorem union_set_cost_le (c : UnionCtx) (ok : c.Ok) (I capacity count : BitVec 64) (le : I.toNat ≤ c.n.toNat)
    (cle : count.toNat ≤ c.count0.toNat + I.toNat)
    (capB : capacity.toNat ≤ c.capacity0.toNat ∨ capacity.toNat ≤ 4 * count.toNat) :
    setBodyCost c.keyLength capacity count ≤
      setBodyCost c.keyLength (BitVec.ofNat 64 c.capMax) (BitVec.ofNat 64 (c.count0.toNat + c.n.toNat)) := by
  obtain ⟨_,_,_,_,_,cap0,n0,c0⟩ := ok
  have cm : c.capMax < 2 ^ 40 := by unfold UnionCtx.capMax; omega
  apply setBodyCost_mono
  · rw [ofNat_toNat_small _ (by omega)]; unfold UnionCtx.capMax; omega
  · rw [ofNat_toNat_small _ (by omega)]; omega
  · rw [ofNat_toNat_small _ (by omega)]; omega

/-- One loop iteration from a ranked state with a remaining item is bounded by the step cost. -/
theorem union_iter_bounded (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (m : Nat) (code : s.code = originalRuntimeCode) (ranked : UnionRank c s m) (I : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I))) (lt : I.toNat < c.n.toNat)
    (budget : c.stepCost ≤ s.clock) : RunBounded s unionIter c.stepCost := by
  obtain ⟨I',iL',ILe,_,_,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,room,
    _,cle,capB,_⟩,⟨p,heap,pLe,pAl,pIn⟩,_⟩ := ranked
  rw [iL] at iL'
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at iL'
  subst iL'
  have okc := ok
  obtain ⟨hdr,_,_,arena,small,_,_,_⟩ := okc
  have costLe := union_set_cost_le c ok I capacity count ILe cle capB
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "src"),.var .local (ofString "i")] = some [.val (.word c.src),.val (.word I)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,srcL,iL]
  unfold unionIter
  unfold UnionCtx.stepCost at budget ⊢
  refine RunBounded.decCall args (by omega) ?_
  intro body locals rs lookup
  rw [pan_two_word_lookup_shape s.code.lookup (ofString "htab_item") (ofString "t") (ofString "ordinal")
    (sourceFunctionBody Guest.guestFn_htab_item) (.comb [.one,.one,.one]) c.src I (by decide)
    (by rw [code]; exact vmLookup_htab_item)] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  refine ⟨?_,?_⟩
  · obtain ⟨ps,bd,rs',lk,pb⟩ := vmBound_htab_item
    rw [vmLookup_htab_item] at lk
    simp only [Option.some.injEq,Prod.mk.injEq] at lk
    obtain ⟨_,rfl,_⟩ := lk
    exact RunBounded.ofProg pb (by exact code) (by change 1 ≤ s.clock - 1; omega)
  · intro value post run tailBudget
    obtain ⟨b,kp,vv,rfl⟩ := union_item_returned c reads s post I lt code addrs mem _ run
    have frame := htabItem_memoryFrame (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (by exact code)
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (sourceFunctionBody Guest.guestFn_htab_item)
    rw [run] at frame meta'
    generalize hT : setVarHOLFinite (ofString "s") (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)])
      {post with locals := s.locals} = T
    have tm : T.memory = s.memory := by rw [← hT]; exact frame.1
    have tg : T.globals = s.globals := by rw [← hT]; exact frame.2
    have ta : T.memaddrs = s.memaddrs := by rw [← hT]; exact meta'.2.1
    have tb : T.be = s.be := by rw [← hT]; exact meta'.2.2.1
    have tc : T.code = s.code := by rw [← hT]; exact meta'.1
    have tk : T.clock = post.clock := by rw [← hT]; rfl
    have tS : T.locals.lookup (ofString "s") = some (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)]) := by
      rw [← hT]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have tD : T.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := by
      rw [← hT]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,dL]
    refine RunBounded.seq (a := setBodyCost c.keyLength (BitVec.ofNat 64 c.capMax)
      (BitVec.ofNat 64 (c.count0.toNat + c.n.toNat)) + 1) (b := 0) ?_ (by omega) ?_
    · obtain ⟨gw,guard⟩ := union_guard_word T b kp vv tS
      unfold unionSetIte
      refine RunBounded.iteWord T _ gw guard (fun _ => ?_) (fun _ => ?_)
      · refine RunBounded.weaken (runBounded_htabSet_call_laid T none _ _ _ c.keyLength c.dst keys c.stride capacity used
          values order orderPos count kp vv p bits lo hi (laid.transfer tm ta tb tc) (union_set_args T c.dst b kp vv tD tS)
          (by rw [tg]; exact heap) pAl (by omega) pIn (fun a h1 h2 h3 => by rw [ta,addrs]; exact arena a h1 h2 h3) room small
          (by omega)) (by omega)
      · exact RunBounded.weaken (RunBounded.ofProg (ProgBounded.straight _ (by decide)) (tc.trans code) (Nat.zero_le _))
          (Nat.zero_le _)
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans (tc.trans code)) (Nat.zero_le _)

#print axioms union_iter_bounded

/-- A normal loop iteration advances the counter and keeps the rank invariant. -/
theorem union_iter_normal (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (m : Nat) (code : s.code = originalRuntimeCode) (ranked : UnionRank c s (m + 1)) (I : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I))) (lt : I.toNat < c.n.toNat)
    (budget : c.stepCost ≤ s.clock)
    (run : evaluateHOLFiniteState s unionIter = (none,post)) :
    UnionRank c post m ∧ post.code = s.code := by
  obtain ⟨I',iL',ILe,left,capL,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,room,
    c0le,cle,capB,loB⟩,⟨p,heap,pLe,pAl,pIn⟩,rel⟩ := ranked
  rw [iL] at iL'
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at iL'
  subst iL'
  have okc := ok
  obtain ⟨hdr,_,_,arena,small,cap0,n0,c0⟩ := okc
  have costLe := union_set_cost_le c ok I capacity count ILe cle capB
  have noWrap : (I + 1).toNat = I.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change I.toNat + 1 < 2 ^ 64; omega)]; rfl
  unfold unionIter at run
  obtain ⟨vals,body,callee,rs,w,bodyPost,resumed,inner,args',lookup',bodyRun,rm,ra,rb,rc,rg,rclk,rname,rothers,contRun,
    pm,pa,pb,pc,pg,plocals⟩ := decCall_normal_globals run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "src"),.var .local (ofString "i")] = some [.val (.word c.src),.val (.word I)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,srcL,iL]
  rw [args] at args'
  simp only [Option.some.injEq] at args'
  subst args'
  rw [pan_two_word_lookup_shape s.code.lookup (ofString "htab_item") (ofString "t") (ofString "ordinal")
    (sourceFunctionBody Guest.guestFn_htab_item) (.comb [.one,.one,.one]) c.src I (by decide)
    (by rw [code]; exact vmLookup_htab_item)] at lookup'
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup'
  obtain ⟨rfl,rfl,rfl⟩ := lookup'
  obtain ⟨b,kp,vv,rfl⟩ := union_item_returned c reads s bodyPost I lt code addrs mem _ bodyRun
  have frame := htabItem_memoryFrame (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
    (by exact code)
  have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
    (sourceFunctionBody Guest.guestFn_htab_item)
  rw [bodyRun] at frame meta'
  have resClock : s.clock - 2 ≤ resumed.clock := by
    obtain ⟨ps,bd,rs',lk,pb⟩ := vmBound_htab_item
    rw [vmLookup_htab_item] at lk
    simp only [Option.some.injEq,Prod.mk.injEq] at lk
    obtain ⟨_,rfl,_⟩ := lk
    have h := pb (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (by exact code) (by change 1 ≤ s.clock - 1; unfold UnionCtx.stepCost at budget; omega)
    rw [bodyRun] at h
    obtain ⟨h1,h2,_⟩ := h
    change s.clock - 1 ≤ bodyPost.clock + 1 at h1
    rw [rclk h2]
    omega
  have qm : resumed.memory = s.memory := rm.trans frame.1
  have qg : resumed.globals = s.globals := rg.trans frame.2
  have qa : resumed.memaddrs = s.memaddrs := ra.trans meta'.2.1
  have qb : resumed.be = s.be := rb.trans meta'.2.2.1
  have qc : resumed.code = s.code := rc.trans meta'.1
  have qD : resumed.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := (rothers _ (by decide)).trans dL
  have qI : resumed.locals.lookup (ofString "i") = some (.val (.word I)) := (rothers _ (by decide)).trans iL
  rw [evaluateHOLFiniteState_seq_line780] at contRun
  cases iteRun : evaluateHOLFiniteState resumed unionSetIte with
  | mk ir mid =>
    rw [iteRun] at contRun
    cases ir with
    | some r => simp at contRun
    | none =>
      simp only at contRun
      have key : mid.locals = resumed.locals ∧ mid.memaddrs = c.A0 ∧ mid.code = s.code ∧
          (∀ w, c.Away w → mid.memory w = c.M0 w) ∧ c.Dst (I + 1) mid ∧ c.Heap mid := by
        unfold unionSetIte at iteRun
        rcases ite_normal_cases_cond resumed mid _ _ _ iteRun with ⟨gw,_,_,setRun⟩ | ⟨_,skipRun⟩
        · obtain ⟨⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',counts,capB',loB'⟩,mlocals,maddrs,mbe,mframe⟩ :=
            htabSet_call_normal_laid resumed mid _ _ _ c.keyLength c.dst keys c.stride capacity used values order orderPos
              count kp vv p bits lo hi (laid.transfer qm qa qb qc) (union_set_args resumed c.dst b kp vv qD rname)
              (by rw [qg]; exact heap) pAl (by omega) pIn (fun a h1 h2 h3 => by rw [qa,addrs]; exact arena a h1 h2 h3)
              (tables.transfer qm qa qb) room small (by unfold UnionCtx.stepCost at budget; omega) setRun
          have setRel : HeapRel resumed.globals mid.globals := by
            have := normalRel_apply (htabSet_call_normalRel
              [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
              (X := resumed) (by rw [setRun]; exact Or.inl rfl) (qc.trans code)
            rw [setRun] at this
            exact this
          rw [qg] at setRel
          have midMeta := evaluateHOLFiniteState_metadata resumed (.call (some (none,none)) (ofString "htab_set")
            [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
          rw [setRun] at midMeta
          obtain ⟨p1,heap1,pp1,a1,i1⟩ := setRel.2 p heap pAl pIn
          refine ⟨mlocals,maddrs.trans (qa.trans addrs),midMeta.1.trans qc,fun w away => ?_,?_,
            ⟨⟨p1,heap1,by omega,a1,i1⟩,heapRel_preorder.trans _ _ _ rel setRel⟩⟩
          · obtain ⟨wp,wh,wl⟩ := away
            rw [mframe w (by omega) wh (by rcases loB with ⟨rfl,rfl⟩ | lp <;> omega),qm]
            exact mem w ⟨wp,wh,wl⟩
          · refine ⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',?_,?_,?_,?_,?_⟩
            · rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rw [noWrap]; rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rcases capB' with rfl | lt4
              · rcases counts with ⟨_,rfl⟩ | ⟨e1,e2⟩ <;> omega
              · omega
            · rcases loB' with ⟨rfl,rfl⟩ | lp
              · exact loB
              · omega
        · rw [evaluateHOLFiniteState_skip] at skipRun
          obtain ⟨_,rfl⟩ := Prod.mk.inj skipRun
          refine ⟨rfl,qa.trans addrs,qc,fun w away => by rw [qm]; exact mem w away,
            ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer qm qa qb qc,tables.transfer qm qa qb,
              room,c0le,by rw [noWrap]; omega,capB,loB⟩,⟨⟨p,by rw [qg]; exact heap,pLe,pAl,pIn⟩,by rw [qg]; exact rel⟩⟩
      obtain ⟨mlocals,maddrs,mcode,mmem,⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',r1,r2,r3,r4,r5⟩,
        ⟨p1,heap1,pp1,a1,i1⟩,rel1⟩ := key
      have mI : mid.locals.lookup (ofString "i") = some (.val (.word I)) := by rw [mlocals]; exact qI
      unfold unionIncr at contRun
      rw [evaluate_increment_local mid (ofString "i") I mI] at contRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj contRun
      have keep : ∀ x, x ≠ ofString "s" → x ≠ ofString "i" → post.locals.lookup x = s.locals.lookup x := by
        intro x ns ni
        rw [plocals x ns]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
        rw [mlocals]
        exact rothers x ns
      refine ⟨⟨I + 1,?_,by rw [noWrap]; omega,by rw [noWrap]; omega,
        by rw [keep _ (by decide) (by decide)]; exact capL,
        by rw [keep _ (by decide) (by decide)]; exact dL,
        by rw [keep _ (by decide) (by decide)]; exact srcL,
        pa.trans maddrs,fun w away => by rw [pm]; exact mmem w away,
        ⟨c',k',u',v',o',op',n',b',lo',hi',laid'.transfer pm pa pb pc,tables'.transfer pm pa pb,r1,r2,r3,r4,r5⟩,
        ⟨⟨p1,by rw [pg]; exact heap1,pp1,a1,i1⟩,by rw [pg]; exact rel1⟩⟩,pc.trans mcode⟩
      rw [plocals _ (by decide)]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms union_iter_normal

theorem unionLoop_shape : (.while unionCond unionIter : ProgHOL 64) =
    .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
      (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
        [.var .local (ofString "src"),.var .local (ofString "i")]
        (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
            (.call (some (none,none)) (ofString "htab_set")
              [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := rfl

theorem UnionRank.transfer (c : UnionCtx) {F : Type} {s r : PanSemStateFiniteExact 64 F} {m : Nat}
    (ranked : UnionRank c s m) (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be)
    (code : r.code = s.code) (globals : r.globals = s.globals) (locals : r.locals = s.locals) : UnionRank c r m := by
  obtain ⟨I,iL,a1,a2,capL,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩,
    ⟨⟨p,heap,h1,h2,h3⟩,rel⟩⟩ := ranked
  exact ⟨I,by rw [locals]; exact iL,a1,a2,by rw [locals]; exact capL,by rw [locals]; exact dL,by rw [locals]; exact srcL,
    memaddrs.trans addrs,fun w away => by rw [memory]; exact mem w away,
    ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer memory memaddrs be code,
      tables.transfer memory memaddrs be,r1,r2,r3,r4,r5⟩,⟨⟨p,by rw [globals]; exact heap,h1,h2,h3⟩,by rw [globals]; exact rel⟩⟩

/-- The union loop from rank m runs within m * (stepCost + 1) ticks, and a normal exit keeps the rank. -/
theorem unionLoop_run (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      UnionRank c state m → m * (c.stepCost + 1) ≤ state.clock →
      RankedOutcome state unionCond (m * (c.stepCost + 1)) (UnionRank c) False
        (evaluateHOLFiniteState state (.while unionCond unionIter)) := by
  have nSmall : c.n.toNat < 2 ^ 63 := by obtain ⟨_,_,_,_,_,_,n0,_⟩ := ok; omega
  refine rankedWhile_run _ unionIter c.stepCost (UnionRank c) False ?_ ?_
  · intro F s ranked v hv
    obtain ⟨I,iL,ILe,left,capL,_⟩ := ranked
    unfold unionCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have : ¬ I.toNat < c.n.toNat := by omega
    simp [this] at hv
    exact hv.symm
  · intro F s m v code' ranked hv nonzero budget'
    have rankedD : UnionRank c (decClockHOLFinite s) (m + 1) := ranked.transfer c rfl rfl rfl rfl rfl rfl
    obtain ⟨I,iL,ILe,left,capL,_⟩ := ranked
    unfold unionCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have lt : I.toNat < c.n.toNat := by
      by_cases h : I.toNat < c.n.toNat
      · exact h
      · simp [h] at hv; exact absurd hv.symm nonzero
    have bounded := union_iter_bounded c ok reads (decClockHOLFinite s) (m + 1) code' rankedD I iL lt
      (by change _ ≤ s.clock - 1; omega)
    obtain ⟨b1,b2,b3⟩ := bounded
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases hrun : evaluateHOLFiniteState (decClockHOLFinite s) unionIter with
        | mk r post =>
          rw [hrun] at normal
          simp only at normal
          subst normal
          obtain ⟨rk,pc⟩ := union_iter_normal c ok reads (decClockHOLFinite s) post m code' rankedD I iL lt
            (by change _ ≤ s.clock - 1; omega) hrun
          exact ⟨m,le_refl _,rk,pc⟩
      · exact absurd cont (evaluate_noTopContinue unionIter (by decide) (decClockHOLFinite s))
    · intro brk
      exact absurd brk (evaluate_noTopBreak unionIter (by decide) (decClockHOLFinite s))

#print axioms unionLoop_run

theorem unionIter_not_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s unionIter = (some (.returned v),post)) : False := by
  unfold unionIter at run
  obtain ⟨_,_,_,_,_,_,resumed,_,_,_,_,_,_,_,_,_,_,_,contRun,_⟩ := decCall_returned_body run
  rw [evaluateHOLFiniteState_seq_line780] at contRun
  cases iteRun : evaluateHOLFiniteState resumed unionSetIte with
  | mk ir mid =>
    rw [iteRun] at contRun
    cases ir with
    | none =>
      simp only at contRun
      unfold unionIncr at contRun
      rw [evaluateHOLFiniteState_assign] at contRun
      split at contRun <;> (try split at contRun) <;> simp at contRun
    | some r =>
      obtain ⟨e,_⟩ := Prod.mk.inj contRun
      simp only [Option.some.injEq] at e
      subst e
      unfold unionSetIte at iteRun
      rw [evaluateHOLFiniteState_ite] at iteRun
      split at iteRun
      · split at iteRun
        · simp [evaluateHOLFiniteState_skip] at iteRun
        · exact discard_call_not_returned resumed _ _ v (by rw [iteRun])
      · simp at iteRun

theorem unionLoop_not_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.while unionCond unionIter) = (some (.returned v),post)) : False :=
  while_returned_invariant _ unionIter (fun _ => True) (fun _ => False) (fun _ _ => trivial)
    (fun t w q _ r => unionIter_not_returned t q w r) (fun _ _ _ _ => trivial) s.clock s rfl trivial v post run

theorem dec_returned_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (some (.returned v),post)) :
    ∃ value inner, @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
        initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      post.globals = inner.globals := by
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
        exact ⟨value,i,evaluated,by rw [inner,e],rfl,rfl,rfl,rfl,rfl⟩
    · simp at run

theorem return_const_globals {F : Type} (s post : PanSemStateFiniteExact 64 F) (k : BitVec 64) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.return (.const k)) = (some (.returned v),post)) :
    v = .val (.word k) ∧ post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      post.globals = s.globals := by
  rw [evaluateHOLFiniteState_return] at run
  simp only [eval_const_word] at run
  split at run
  · obtain ⟨e,rfl⟩ := Prod.mk.inj run
    simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at e
    exact ⟨e.symm,rfl,rfl,rfl,rfl,rfl⟩
  · simp at run

/-- The original `htab_union_into` body, from a destination table of either actual layout and a
source whose read words are mapped, word-valued and away from the destination footprint: it returns
0 with a destination table of either layout at count ≤ count0 + n, the heap pointer only grown, and
every word below the entry heap pointer outside the destination header and initial block unchanged. -/
theorem htabUnionInto_returned (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (dstL : state.locals.lookup (ofString "dst") = some (.val (.word c.dst)))
    (srcL : state.locals.lookup (ofString "src") = some (.val (.word c.src)))
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_union_into) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ c.Dst c.n post ∧ c.Heap post ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      ∀ w, c.Away w → post.memory w = state.memory w := by
  have okc := ok
  obtain ⟨_,pAl,pIn,_,_,_,_,c0⟩ := okc
  rw [source_htabUnionInto_body] at run
  obtain ⟨cv,s1r,e1,run1,m1,a1,b1,k1,g1⟩ := dec_returned_globals run
  rw [eval_load_word state _ (c.src + 24) c.n (eval_add2 state _ _ c.src 24 (item_eval_locals state _ _ srcL)
    (item_eval_const state 24)) nDomain nCell] at e1
  cases e1
  obtain ⟨iv,s2r,e2,run2,m2,a2,b2,k2,g2⟩ := dec_returned_globals run1
  rw [item_eval_const] at e2
  cases e2
  generalize hs2 : setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "cap") (.val (.word c.n)) state) = s2 at run2
  have rank0 : UnionRank c s2 c.n.toNat := by
    obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
    rw [← hs2]
    refine ⟨0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,dstL],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,srcL],
      memaddrs0.symm,fun w _ => by rw [memory0]; rfl,
      ⟨c.capacity0,keys,used,values,order,orderPos,c.count0,bits,c.lo0,c.hi0,laid.transfer rfl rfl rfl rfl,
        tables.transfer rfl rfl rfl,c0,le_refl _,by simp,Or.inl (le_refl _),Or.inl ⟨rfl,rfl⟩⟩,
      ⟨⟨c.pointer0,heap,le_refl _,pAl,pIn⟩,by rw [globals0]; exact heapRel_preorder.refl _⟩⟩
  have s2code : s2.code = originalRuntimeCode := by rw [← hs2]; exact code
  have s2clock : s2.clock = state.clock := by rw [← hs2]; rfl
  have s2meta : s2.memory = state.memory ∧ s2.memaddrs = state.memaddrs ∧ s2.be = state.be ∧ s2.globals = state.globals := by
    rw [← hs2]; exact ⟨rfl,rfl,rfl,rfl⟩
  rw [evaluateHOLFiniteState_seq_line780] at run2
  cases loopRun : evaluateHOLFiniteState s2 (.while unionCond unionIter) with
  | mk lr ls =>
    have outcome := unionLoop_run c ok reads c.n.toNat s2 s2code rank0 (by rw [s2clock]; exact budget)
    have loopShape : (.while unionCond unionIter : ProgHOL 64) =
        .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
          (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
            [.var .local (ofString "src"),.var .local (ofString "i")]
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none,none)) (ofString "htab_set")
                  [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := rfl
    rw [← loopShape,loopRun] at run2
    rw [loopRun] at outcome
    cases lr with
    | some r =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run2
      simp only [Option.some.injEq] at e
      subst e
      exact unionLoop_not_returned s2 ls v loopRun
    | none =>
      simp only at run2
      obtain ⟨_,_,_,normal⟩ := outcome
      obtain ⟨m,rk,lcode,_⟩ := normal rfl
      obtain ⟨ve,rm,ra,rb,rc,rg⟩ := return_const_globals ls s2r 0 v run2
      obtain ⟨I,_,ILe,_,_,_,_,laddrs,lmem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩,
        heapL⟩ := rk
      have pPost : post.memory = ls.memory ∧ post.memaddrs = ls.memaddrs ∧ post.be = ls.be ∧ post.code = ls.code ∧
          post.globals = ls.globals :=
        ⟨m1.trans (m2.trans rm),a1.trans (a2.trans ra),b1.trans (b2.trans rb),k1.trans (k2.trans rc),g1.trans (g2.trans rg)⟩
      have lmeta := evaluateHOLFiniteState_metadata s2 (.while unionCond unionIter)
      rw [loopRun] at lmeta
      refine ⟨ve,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,
          laid.transfer pPost.1 pPost.2.1 pPost.2.2.1 pPost.2.2.2.1,tables.transfer pPost.1 pPost.2.1 pPost.2.2.1,
          r1,r2,by omega,r4,r5⟩,?_,pPost.2.1.trans (lmeta.2.1.trans s2meta.2.1),
        pPost.2.2.1.trans (lmeta.2.2.1.trans s2meta.2.2.1),pPost.2.2.2.1.trans (lcode.trans (s2code.trans code.symm)),
        fun w away => by rw [pPost.1,lmem w away,memory0]⟩
      obtain ⟨⟨p,hp,h1,h2,h3⟩,rel⟩ := heapL
      exact ⟨⟨p,by rw [pPost.2.2.2.2]; exact hp,h1,h2,h3⟩,by rw [pPost.2.2.2.2]; exact rel⟩

#print axioms htabUnionInto_returned

theorem evaluate_discard_normal_body_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.locals = state.locals ∧ post.globals = output.globals ∧
      post.memaddrs = output.memaddrs ∧ post.be = output.be ∧ post.code = output.code := by
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
          · refine ⟨value,output,rfl,?_,?_,?_,?_,?_,?_⟩
            all_goals rw [← (Prod.mk.inj run).2]
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | finalFfi ffi => cases run
        | exception exceptionId value => cases run

theorem htabUnionInto_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (dst src : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htab_union_into") [.val (.word dst),.val (.word src)] =
      some (sourceFunctionBody Guest.guestFn_htab_union_into,
        (HolFiniteMapExact.empty.update (ofString "dst",.val (.word dst))).update (ofString "src",.val (.word src)),.one) :=
  pan_two_word_lookup state.code.lookup (ofString "htab_union_into") (ofString "dst") (ofString "src")
    (sourceFunctionBody Guest.guestFn_htab_union_into) dst src (by decide)
    (by rw [code]; exact originalRuntimeCode_htabUnionInto_lookup)

/-- The discarded `htab_union_into(dst, src)` call with the contract of `htabUnionInto_returned`. -/
theorem htabUnionInto_call_normal (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (dstArgument srcArgument : ExpHOL 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word c.dst),.val (.word c.src)])
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) =
      (none,post)) :
    c.Dst c.n post ∧ c.Heap post ∧ post.locals = state.locals ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      ∀ w, c.Away w → post.memory w = state.memory w := by
  obtain ⟨v,output,bodyRun,pm,pl,pg,pa,pb,pc⟩ := evaluate_discard_normal_body_globals state post _ _ _ _ _ _ args
    (htabUnionInto_installed state c.dst c.src code) run
  obtain ⟨_,dst,heapO,oa,ob,oc,frame⟩ := htabUnionInto_returned c ok reads (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word c.dst))).update (ofString "src",.val (.word c.src)))) output v (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact nDomain) (by exact nCell) (by exact memory0) (by exact memaddrs0) (by exact globals0)
    (by
      obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
      exact ⟨keys,used,values,order,orderPos,bits,laid.transfer rfl rfl rfl rfl,tables.transfer rfl rfl rfl⟩)
    (by exact heap) (by change _ ≤ state.clock - 1; omega) bodyRun
  obtain ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩ := dst
  obtain ⟨⟨p,hp,h1,h2,h3⟩,rel⟩ := heapO
  exact ⟨⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer pm pa pb pc,tables.transfer pm pa pb,
      r1,r2,r3,r4,r5⟩,⟨⟨p,by rw [pg]; exact hp,h1,h2,h3⟩,by rw [pg]; exact rel⟩,pl,pa.trans oa,pb.trans ob,pc.trans oc,
    fun w away => by rw [pm]; exact frame w away⟩

#print axioms htabUnionInto_call_normal

set_option maxHeartbeats 1000000 in
/-- The `htab_union_into(dst, src)` call costs at most n * (stepCost + 1) + 1 ticks in every outcome. -/
theorem runBounded_htabUnionInto_call (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS)) (dstArgument srcArgument : ExpHOL 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word c.dst),.val (.word c.src)])
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_union_into") [dstArgument,srcArgument])
      (c.n.toNat * (c.stepCost + 1) + 1) := by
  have okc := ok
  obtain ⟨_,pAl,pIn,_,_,_,_,c0⟩ := okc
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabUnionInto_installed state c.dst c.src code] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  generalize hE : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word c.dst))).update (ofString "src",.val (.word c.src))) = E
  have eD : E.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := by
    rw [← hE]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eS : E.locals.lookup (ofString "src") = some (.val (.word c.src)) := by
    rw [← hE]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eM : E.memory = state.memory ∧ E.memaddrs = state.memaddrs ∧ E.be = state.be ∧ E.code = state.code ∧
      E.globals = state.globals ∧ E.clock = state.clock - 1 := by rw [← hE]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [source_htabUnionInto_body]
  refine RunBounded.decWord E _ _ c.n (eval_load_word E _ (c.src + 24) c.n
    (eval_add2 E _ _ c.src 24 (item_eval_locals E _ _ eS) (item_eval_const E 24))
    (by rw [eM.2.1]; exact nDomain) (by rw [eM.1]; exact nCell)) ?_
  refine RunBounded.decConst _ _ _ ?_
  generalize hs2 : setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "cap") (.val (.word c.n)) E) = s2
  have rank0 : UnionRank c s2 c.n.toNat := by
    obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
    rw [← hs2]
    refine ⟨0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,eD],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,eS],
      by rw [memaddrs0]; exact eM.2.1,fun w _ => by rw [memory0]; exact congrFun eM.1 w,
      ⟨c.capacity0,keys,used,values,order,orderPos,c.count0,bits,c.lo0,c.hi0,
        laid.transfer eM.1 eM.2.1 eM.2.2.1 eM.2.2.2.1,tables.transfer eM.1 eM.2.1 eM.2.2.1,c0,le_refl _,by simp,
        Or.inl (le_refl _),Or.inl ⟨rfl,rfl⟩⟩,
      ⟨⟨c.pointer0,by change E.globals.lookup _ = _; rw [eM.2.2.2.2.1]; exact heap,le_refl _,pAl,pIn⟩,
        by change HeapRel c.G0 E.globals; rw [eM.2.2.2.2.1,globals0]; exact heapRel_preorder.refl _⟩⟩
  have s2code : s2.code = originalRuntimeCode := by rw [← hs2]; change E.code = _; rw [eM.2.2.2.1]; exact code
  have s2clock : s2.clock = state.clock - 1 := by rw [← hs2]; exact eM.2.2.2.2.2
  have whole : RunBounded s2 (.seq (.while unionCond unionIter) (.return (.const 0)))
      (c.n.toNat * (c.stepCost + 1) + 0) := by
    refine RunBounded.seq ?_ (by rw [s2clock]; omega) ?_
    · obtain ⟨o1,o2,o3,_⟩ := unionLoop_run c ok reads c.n.toNat s2 s2code rank0 (by rw [s2clock]; omega)
      exact ⟨o1,o2,o3⟩
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans s2code) (Nat.zero_le _)
  rw [Nat.add_zero,unionLoop_shape] at whole
  exact whole

#print axioms runBounded_htabUnionInto_call
end InitECandidate.Runtime
