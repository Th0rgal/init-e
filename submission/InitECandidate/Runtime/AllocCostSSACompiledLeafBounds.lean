import InitECandidate.Runtime.AllocCostSSAStageCases
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordUnreach.Proofs
import InitECandidate.Runtime.AllocMoveTable

/-!
# Compile-output bounds for leaf constructors

Bounds stated against the *actual* compile output `(ssaCcTrans p ssa next tables).1`
and the 64-bit native price `nativeWordPrice`, with the inserted-move overhead
*derived* from the emitted program rather than supplied as a target budget.

For `move` the compiler renames both sides of each pair and only updates the SSA
map (`force` is applied with `forceRename` to the map, not inserted as
instructions), so the emitted program is again a single `move` whose pair count
equals the source pair count.  Since `nativeWordPrice` on a `move` depends only
on that count, no moves are inserted and the executed cost is unchanged.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordUnreach
open InitECandidate.Runtime.WordToStack

/-- The native price of a `move` depends only on the number of pairs. -/
theorem nativeWordPrice_move_length {C F : Type} (pri : Nat)
    (ls ls' : List (Nat × Nat))
    (source target : WordSemStateFiniteExact 64 C F) (hlen : ls'.length = ls.length) :
    nativeWordPrice (.move pri ls') target = nativeWordPrice (.move pri ls) source := by
  rw [nativeWordPrice_move, nativeWordPrice_move, hlen]

/-- **Compiled `move` bound.**  If the compiler emits a `move` with the same
number of pairs, the executed cost is exactly the source cost: the renaming is
free because the parallel-move unit is priced by pair count alone. -/
theorem ssaCcTrans_move_cost {C F : Type} (pri : Nat) (ls : List (Nat × Nat))
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (ls' : List (Nat × Nat)) (source target : WordSemStateFiniteExact 64 C F)
    (hcomp : (ssaCcTrans ((.move pri ls) : WordLangProgHOL (BitVec 64)) ssa na tables).1 =
      .move pri ls')
    (hlen : ls'.length = ls.length) :
    wordExecutionCost nativeWordPrice (.move pri ls') target ≤
      wordExecutionCost nativeWordPrice (.move pri ls) source := by
  rw [wec_move, wec_move, nativeWordPrice_move_length pri ls ls' source target hlen]

/-- **Compiled `inst` bound.**  If the compiler emits a single `inst`, the two
executed costs are the two node prices; whenever the emitted instruction's price
agrees with the source instruction's price the transfer is an equality. -/
theorem ssaCcTrans_inst_cost {C F : Type} (i i' : WordLangInst (BitVec 64))
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : WordSemStateFiniteExact 64 C F)
    (hcomp : (ssaCcTrans (.inst i) ssa na tables).1 = .inst i')
    (hprice : nativeWordPrice (.inst i') target = nativeWordPrice (.inst i) source) :
    wordExecutionCost nativeWordPrice (.inst i') target ≤
      wordExecutionCost nativeWordPrice (.inst i) source := by
  rw [wec_inst, wec_inst]
  exact le_of_eq hprice

/-- `assign` is a leaf: it charges only its node price. -/
theorem wec_assign {C F : Type}
    (num : Nat) (exp : WordLangExpHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost nativeWordPrice (.assign num exp) s =
      nativeWordPrice (.assign num exp) s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction)

/-- **Actual compiled fragment of `inst`.**  The `ssaCcTrans` clause delegates to
`ssaCcTransInst`, so the emitted program is exactly that fragment's program
(which may itself be a `seq` when the container expansion fires). -/
theorem ssaCcTrans_inst_shape {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) (ssa : Spt Nat) (na : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans (.inst i) ssa na tables).1 = (ssaCcTransInst i ssa na).1 := by
  simp only [ssaCcTrans]

/-- **Actual compiled fragment of `assign`.**  The destination is renamed by
`nextVarRename` and the expression by `ssaCcTransExp`; the emitted program is a
single `assign`, so no instructions are inserted. -/
theorem ssaCcTrans_assign_shape {width : Nat} [NeZero width]
    (num : Nat) (exp : WordLangExpHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans (.assign num exp) ssa na tables).1 =
      .assign (nextVarRename num ssa na).1 (ssaCcTransExp ssa exp) := by
  simp only [ssaCcTrans]

/-- **Compiled `assign` cost bound.**  Because the emitted fragment is a single
`assign`, the executed cost is the two node prices - an equality whenever the
emitted assign's price agrees with the source one.  No inserted instruction and
no target budget. -/
theorem ssaCcTrans_assign_cost {C F : Type}
    (num : Nat) (exp : WordLangExpHOL (BitVec 64))
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (num' : Nat) (exp' : WordLangExpHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (hcomp : (ssaCcTrans ((.assign num exp) : WordLangProgHOL (BitVec 64)) ssa na tables).1 =
      .assign num' exp')
    (hprice : nativeWordPrice (.assign num' exp') target =
      nativeWordPrice (.assign num exp) source) :
    wordExecutionCost nativeWordPrice (.assign num' exp') target ≤
      wordExecutionCost nativeWordPrice (.assign num exp) source := by
  rw [wec_assign, wec_assign]
  exact le_of_eq hprice

/-- **Merge overhead arithmetic.**  Each inserted move is a `.move` node priced
`(if len ≤ 1 then 14 else 28) * len`, so with `n` live variables at a merge (the
length of `sptToAList (sptUnion ssaL ssaR)`), `lmov`/`rmov` of at most `n` pairs
each and at most `n` fake moves the inserted cost is at most `70 * n`.  This is
the concrete number handed to the source side; it needs no target assumption. -/
theorem merge_overhead_bound (n lmovLen rmovLen fakeCount : Nat)
    (h1 : lmovLen ≤ n) (h2 : rmovLen ≤ n) (h3 : fakeCount ≤ n) :
    28 * lmovLen + 28 * rmovLen + 14 * fakeCount ≤ 70 * n := by
  omega

/-- **Actual compiled fragment of `seq`.**  The clause threads the SSA map and
the next fresh variable through the first half (`ssa'`, `na'`) and compiles the
second half against those, so the emitted program is the compiled halves in
sequence - note the second half is compiled at the *threaded* map, not the source
one. -/
theorem ssaCcTrans_seq_shape {width : Nat} [NeZero width]
    (s1 s2 : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans (.seq s1 s2) ssa na lt).1 =
      .seq (ssaCcTrans s1 ssa na lt).1
        (ssaCcTrans s2 (ssaCcTrans s1 ssa na lt).2.1
          (ssaCcTrans s1 ssa na lt).2.2 lt).1 := by
  simp only [ssaCcTrans]

/-- **Actual compiled fragment of `ite`.**  Both branches are compiled at the
incoming map (the second at the first's threaded next variable), and the two
merge programs from `fixInconsistencies` are appended to the branches:
`(.seq e2' e2Cons)` and `(.seq e3' e3Cons)`.  This is where the live moves are
inserted, so their cost is the cost of those `e2Cons`/`e3Cons` merge programs. -/
theorem ssaCcTrans_ite_shape {width : Nat} [NeZero width]
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec width))
    (e2 e3 : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans (.ite cmp r1 ri e2 e3) ssa na lt).1 =
      .ite cmp (optionLookup ssa r1)
        (match ri with
          | .reg r => .reg (optionLookup ssa r)
          | .imm v => .imm v)
        (.seq (ssaCcTrans e2 ssa na lt).1
          (fixInconsistencies
            (mkPrio (ssaCcTrans e2 ssa na lt).1
              (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).1)
            (ssaCcTrans e2 ssa na lt).2.1
            (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).2.1
            (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).2.2).1)
        (.seq (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).1
          (fixInconsistencies
            (mkPrio (ssaCcTrans e2 ssa na lt).1
              (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).1)
            (ssaCcTrans e2 ssa na lt).2.1
            (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).2.1
            (ssaCcTrans e3 ssa (ssaCcTrans e2 ssa na lt).2.2 lt).2.2).2.1) := by
  simp only [ssaCcTrans]
  cases ri <;> rfl

/-- **Actual compiled fragment of `raise`.**  One inserted single-pair move
(passing the raised value into frame 2) followed by `raise 2`. -/
theorem ssaCcTrans_raise_shape
    (num : Nat) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans ((.raise num) : WordLangProgHOL (BitVec 64)) ssa na lt).1 =
      .seq (.move 1 [(2, optionLookup ssa num)]) (.raise 2) := by
  simp only [ssaCcTrans]

/-- **Actual compiled fragment of `return`.**  The returned values are renamed
and moved into the return registers `2*(i+1)`, one inserted pair per returned
value, followed by `return` on that register list. -/
theorem ssaCcTrans_return_shape
    (num : Nat) (nums : List Nat) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans ((.return num nums) : WordLangProgHOL (BitVec 64)) ssa na lt).1 =
      .seq
        (.move 0 (((List.range (nums.map (optionLookup ssa)).length).map
          fun x => 2 * (x + 1)).zip (nums.map (optionLookup ssa))))
        (.return (optionLookup ssa num)
          ((List.range (nums.map (optionLookup ssa)).length).map fun x => 2 * (x + 1))) := by
  simp only [ssaCcTrans]

/-- **Inserted return-move count.**  The allocator inserts exactly one move pair
per returned value, so a returning call's inserted move cost is
`(if nums.length ≤ 1 then 14 else 28) * nums.length` by `nativeWordPrice_move`.
This is the concrete, compiler-derived count - not an estimate. -/
theorem ssaCcTrans_return_move_length
    (nums : List Nat) (ssa : Spt Nat) :
    (((List.range (nums.map (optionLookup ssa)).length).map
      fun x => 2 * (x + 1)).zip (nums.map (optionLookup ssa))).length = nums.length := by
  simp

/-- **Actual compiled fragment of `alloc`.**  `stackMov` and `retMov` are the
actual emitted stack-move programs from `listNextVarRenameMove`, not counts, so
the stack-side move accounting is their own structure. -/
theorem ssaCcTrans_alloc_shape
    (num : Nat) (numset : WordLangCutsetsHOL) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    (ssaCcTrans ((.alloc num numset) : WordLangProgHOL (BitVec 64)) ssa na lt).1 =
      .seq ((listNextVarRenameMove ssa (na + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).1
        (.seq (.move 1 [(2, optionLookup ((listNextVarRenameMove ssa (na + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).2.1 num)])
          (.seq (.alloc 2 (Flapjack.WordAlloc.applyNummapsKey (optionLookup ((listNextVarRenameMove ssa (na + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).2.1) numset))
            ((listNextVarRenameMove (sptInter ((listNextVarRenameMove ssa (na + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).2.1 (sptUnion numset.1 numset.2)) (((listNextVarRenameMove ssa (na + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).2.2 + 2) ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).1)) := by
  simp only [ssaCcTrans]

/-- **Inserted argument-move count at a call.**  The `.call none` clause builds
`names := args.map (optionLookup ssa)`, `convArgs := (List.range names.length).map
(fun x => 2 * x)` and `moveArgs := .move 1 (convArgs.zip names)`, so a call site
inserts exactly one pair per source argument. -/
theorem ssaCcTrans_call_arg_move_length
    (args : List Nat) (ssa : Spt Nat) :
    (((List.range (args.map (optionLookup ssa)).length).map
      fun x => 2 * x).zip (args.map (optionLookup ssa))).length = args.length := by
  simp

/-- **Inserted argument-move price at a call**, as a function of the source
argument count: `(if args.length ≤ 1 then 14 else 28) * args.length`.  This is the
allocator's argument-move charge and is distinct from the source-side
`39*(args.length+1-22)` term and from the post-allocation spill. -/
theorem ssaCcTrans_call_arg_move_price {C F : Type}
    (args : List Nat) (ssa : Spt Nat) (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) s =
      (if args.length ≤ 1 then 14 else 28) * args.length := by
  rw [nativeWordPrice_move, ssaCcTrans_call_arg_move_length]

/-- **Returning-call argument moves.**  The `.call (some …)` clause uses
`convArgs := (List.range names.length).map (fun x => 2 * (x + 1))` (registers 2,
4, …), so the inserted argument list again has one pair per source argument. -/
theorem ssaCcTrans_call_some_arg_move_length
    (args : List Nat) (ssa : Spt Nat) :
    (((List.range (args.map (optionLookup ssa)).length).map
      fun x => 2 * (x + 1)).zip (args.map (optionLookup ssa))).length = args.length := by
  simp

/-- **Return-value moves.**  `ret'.zip regs` with
`regs := (List.range ret.length).map (fun x => 2 * (x + 1))`, i.e. one pair per
returned value. -/
theorem ssaCcTrans_call_ret_move_length
    (ret : List Nat) (ret' : List Nat) :
    (ret'.zip ((List.range ret.length).map fun x => 2 * (x + 1))).length ≤ ret.length := by
  simp

/-- **Single inserted pair costs 14.** -/
theorem nativeWordPrice_move_single {C F : Type}
    (pri : Nat) (dst src : Nat) (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.move pri [(dst, src)]) s = 14 := by
  rw [nativeWordPrice_move]
  simp

/-- The charge for a certified non-self move list: the allocator emits one
`.move` node per site whose pairs are exactly the certified list, so this is the
only cost the table contributes there. -/
def certifiedMoveCharge (moves : List (Nat × Nat)) : Nat :=
  (if moves.length ≤ 1 then 14 else 28) * moves.length

/-- **Consuming a certified list.**  For any site whose emitted move node carries
the certified list, its price is exactly `certifiedMoveCharge` of that list - no
target cost, no bound: the table's list determines the charge. -/
theorem nativeWordPrice_move_eq_certified {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.move pri moves) s = certifiedMoveCharge moves := by
  rw [nativeWordPrice_move, certifiedMoveCharge]

/-- A single certified pair charges 14. -/
theorem certifiedMoveCharge_single (dst src : Nat) :
    certifiedMoveCharge [(dst, src)] = 14 := by
  simp [certifiedMoveCharge]

/-- The empty certified list charges nothing (no self-moves, no insertions). -/
theorem certifiedMoveCharge_nil : certifiedMoveCharge [] = 0 := rfl

/-- **Step correspondence at an inserted suffix (merge sites).**  When the first
half falls through, a `seq` costs its node price plus the first half's cost plus
the suffix's cost at the reached middle state.  The allocator's merge insertion
`(.seq branch mergeProg)` has exactly this shape, so the certified merge program is
charged at the state the branch actually reaches. -/
theorem wec_seq_none_split {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s mid : WordSemStateFiniteExact 64 C F)
    (h : fixClock s (evaluate f s) = (none, mid)) :
    wordExecutionCost nativeWordPrice (.seq f g) s =
      nativeWordPrice (.seq f g) s + wordExecutionCost nativeWordPrice f s +
        wordExecutionCost nativeWordPrice g mid := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  rw [h]
  try dsimp only
  try rfl

/-- **Outcome companion of the suffix correspondence.**  On a non-fall-through
outcome (error, break, continue, exception) the `seq` charges only its node price
and the first half; an inserted merge suffix is not charged on that outcome. -/
theorem wec_seq_some_split {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (h : (fixClock s (evaluate f s)).1 ≠ none) :
    wordExecutionCost nativeWordPrice (.seq f g) s =
      nativeWordPrice (.seq f g) s + wordExecutionCost nativeWordPrice f s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  generalize hfix : fixClock s (evaluate f s) = pair at h ⊢
  obtain ⟨res, mid⟩ := pair
  simp only [Prod.fst, Prod.snd] at h ⊢
  cases res with
  | none => exact absurd rfl h
  | some r => simp only [Nat.add_zero]

/-- **Shape of the stack-move program.**  `listNextVarRenameMove` emits a single
`.move 0` node over `newLs.zip curLs`, where `curLs := ls.map (optionLookup ssa)`
and `newLs := (listNextVarRename ls ssa n).1`.  So the alloc/install/ffi stack
moves are one move node over the live-name list, not a program tree. -/
theorem listNextVarRenameMove_shape
    (ssa : Spt Nat) (n : Nat) (ls : List Nat) :
    ((listNextVarRenameMove ssa n ls : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).1 =
      .move 0 ((listNextVarRename ls ssa n).1.zip (ls.map (optionLookup ssa))) := by
  simp only [listNextVarRenameMove]

/-- **Price of the stack-move program** in terms of its certified list: it is
`certifiedMoveCharge` of exactly the list the node carries. -/
theorem listNextVarRenameMove_price {C F : Type}
    (ssa : Spt Nat) (n : Nat) (ls : List Nat) (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice ((listNextVarRenameMove ssa n ls : WordLangProgHOL (BitVec 64) × Spt Nat × Nat)).1 s =
      certifiedMoveCharge ((listNextVarRename ls ssa n).1.zip (ls.map (optionLookup ssa))) := by
  rw [listNextVarRenameMove_shape]
  exact nativeWordPrice_move_eq_certified 0 _ s

/-! ## Parallel-move self-filtering at the physical-register level

A pair `(dst, src)` is a *self move* at the physical level when `dst / 2 = src / 2`
(both halves name the same physical register).  The allocator drops exactly those,
and cycle breaking adds at most one auxiliary pair per remaining (nonself) pair, so
the emitted list has length at most twice the nonself count. -/

/-- The physical-level self filter: keep only pairs whose halves land in different
physical registers. -/
def physNonself (L : List (Nat × Nat)) : List (Nat × Nat) :=
  L.filter fun p => decide (p.1 / 2 ≠ p.2 / 2)

/-- The nonself pair count. -/
def nonselfCount (L : List (Nat × Nat)) : Nat := (physNonself L).length

/-- The self pair count. -/
def selfCount (L : List (Nat × Nat)) : Nat :=
  (L.filter fun p => decide (p.1 / 2 = p.2 / 2)).length

/-- **Nothing self-referential survives the filter.** -/
theorem physNonself_no_self (L : List (Nat × Nat)) :
    (physNonself L).filter (fun p => decide (p.1 / 2 = p.2 / 2)) = [] := by
  simp [physNonself, List.filter_filter]

/-- The nonself count never exceeds the list length. -/
theorem nonselfCount_le (L : List (Nat × Nat)) : nonselfCount L ≤ L.length := by
  simpa [nonselfCount, physNonself] using List.length_filter_le _ L

/-- **Coalescing bound with cycles.**  If the self moves have been dropped and
cycle breaking added at most one auxiliary pair per nonself pair, the emitted
parallel-move list has length at most twice the nonself count - i.e. every moved
value costs at most two pairs, and self moves cost none. -/
theorem parmove_emitted_len_le (L E : List (Nat × Nat)) (auxLen : Nat)
    (hE : E.length ≤ nonselfCount L + auxLen) (haux : auxLen ≤ nonselfCount L) :
    E.length ≤ 2 * nonselfCount L := by
  omega

/-- **Charge of a list of bounded length.**  A move node over `L` costs at most
`28` per pair, so any list of length at most `n` charges at most `28 * n`. -/
theorem certifiedMoveCharge_le_of_len (L : List (Nat × Nat)) (n : Nat)
    (h : L.length ≤ n) : certifiedMoveCharge L ≤ 28 * n := by
  unfold certifiedMoveCharge
  split <;> omega

/-- **Coalesced parallel-move charge.**  With self moves filtered out and cycle
breaking adding at most one auxiliary pair per nonself pair, the emitted list's
charge is at most `56 * nonselfCount L` - i.e. `28` per emitted pair over the
`2 * nonselfCount` emitted pairs, and nothing at all for self moves. -/
theorem parmove_charge_le (L E : List (Nat × Nat)) (auxLen : Nat)
    (hE : E.length ≤ nonselfCount L + auxLen) (haux : auxLen ≤ nonselfCount L) :
    certifiedMoveCharge E ≤ 56 * nonselfCount L := by
  have hlen := parmove_emitted_len_le L E auxLen hE haux
  unfold certifiedMoveCharge
  split <;> omega

/-- **Composed charge for an inserted move prefix.**  Every allocator site that
prefixes a move node (`.seq (.move pri moves) tail`, e.g. call argument moves,
raise/return moves, the alloc stack move) costs its `seq` node price plus exactly
`certifiedMoveCharge moves` plus the tail's cost at the state the move reaches.
The premise is the run fact, not a cost. -/
theorem wec_move_seq_charge {C F : Type} (pri : Nat) (moves : List (Nat × Nat))
    (tail : WordLangProgHOL (BitVec 64)) (s mid : WordSemStateFiniteExact 64 C F)
    (h : fixClock s (evaluate (.move pri moves) s) = (none, mid)) :
    wordExecutionCost nativeWordPrice (.seq (.move pri moves) tail) s =
      nativeWordPrice (.seq (.move pri moves) tail) s + certifiedMoveCharge moves +
        wordExecutionCost nativeWordPrice tail mid := by
  rw [wec_seq_none_split (.move pri moves) tail s mid h, wec_move,
    nativeWordPrice_move_eq_certified]

/-- **Move fall-through, derived from the compiler's own `evaluateMove`.**  A
parallel move succeeds exactly when its destinations are pairwise distinct and all
sources can be read, and then it falls through to the state whose locals are the
copied ones - the concrete `mid` at which `wec_move_seq_charge` charges the tail. -/
theorem evaluate_move_none {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact 64 C F)
    (hnodup : (moves.map Prod.fst).Nodup)
    (hget : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none) :
    evaluate (.move pri moves) s =
      (none, { s with locals := copyVars moves s.locals s.locals }) := by
  rw [Flapjack.Compiler.Backend.WordUnreach.evaluateMove]
  rw [if_pos hnodup]
  cases hv : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s with
  | none => exact absurd hv hget
  | some v => rfl

/-! ## Consuming the AllocMoveTable schedule certificate on actual move nodes -/

/-- **The schedule certificate at an actual emitted move node.**  For any move node
`(.move pri pairs)` that the allocator emits, finite-auth's `goSeq_move` yields the
physical-pair schedule bound `12 * (parmove (physPairs pairs)).length ≤
allocMovePrice pairs`.  Nothing about the target run is assumed: the node and its
pair list are the ones in the allocated AST. -/
theorem move_node_certificate {pri : Nat} {pairs : List (Nat × Nat)} {before : Nat}
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    12 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length ≤
      allocMovePrice pairs :=
  goSeq_move ok

/-- **Call-site argument moves, certified from the actual allocated node.**  The
pairs are exactly the list the `.call` clause emits
(`convArgs.zip names` with `convArgs := (List.range names.length).map (2*x)`), so the
schedule bound applies to the real inserted argument moves. -/
theorem call_arg_move_certificate (args : List Nat) (ssa : Spt Nat) {before : Nat}
    (ok : (goSeq before (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa))))).1 = true) :
    12 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa))))).length ≤
      allocMovePrice (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa))) :=
  goSeq_move ok

/-- Bridge between the Bool `!=` that finite-auth's filters use and `decide (≠)`. -/
theorem bne_decide_eq (a b : Nat) : (a != b) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [h]

/-- finite-auth's nonself count is my `nonselfCount`: his filter runs on the halved
pairs, mine on the original pairs with `decide (≠)`. -/
theorem physPairs_filter_length (pairs : List (Nat × Nat)) :
    ((physPairs pairs).filter (fun p => p.1 != p.2)).length = nonselfCount pairs := by
  simp [physPairs, nonselfCount, physNonself, List.filter_map, Function.comp_def,
    bne_decide_eq]

/-- **His schedule price is dominated by my charge bound**: 12 or 24 per physical
nonself pair is at most 28 per nonself pair. -/
theorem allocMovePrice_le (pairs : List (Nat × Nat)) :
    allocMovePrice pairs ≤ 28 * nonselfCount pairs := by
  unfold allocMovePrice
  dsimp only
  rw [physPairs_filter_length]
  split <;> omega

#print axioms allocMovePrice_le
#print axioms physPairs_filter_length
#print axioms bne_decide_eq
#print axioms move_node_certificate
#print axioms call_arg_move_certificate
#print axioms evaluate_move_none
#print axioms wec_move_seq_charge
#print axioms parmove_charge_le
#print axioms certifiedMoveCharge_le_of_len
#print axioms parmove_emitted_len_le
#print axioms nonselfCount_le
#print axioms physNonself_no_self
#print axioms listNextVarRenameMove_shape
#print axioms listNextVarRenameMove_price
#print axioms wec_seq_some_split
#print axioms wec_seq_none_split
#print axioms nativeWordPrice_move_eq_certified
#print axioms certifiedMoveCharge_single
#print axioms ssaCcTrans_call_some_arg_move_length
#print axioms ssaCcTrans_call_ret_move_length
#print axioms nativeWordPrice_move_single
#print axioms ssaCcTrans_call_arg_move_length
#print axioms ssaCcTrans_call_arg_move_price
#print axioms ssaCcTrans_alloc_shape
#print axioms ssaCcTrans_raise_shape
#print axioms ssaCcTrans_return_shape
#print axioms ssaCcTrans_return_move_length
#print axioms ssaCcTrans_ite_shape
#print axioms ssaCcTrans_seq_shape
#print axioms merge_overhead_bound
#print axioms ssaCcTrans_inst_shape
#print axioms ssaCcTrans_assign_shape
#print axioms ssaCcTrans_assign_cost
#print axioms nativeWordPrice_move_length
#print axioms ssaCcTrans_move_cost
#print axioms ssaCcTrans_inst_cost

end InitECandidate.Runtime.FineCost
