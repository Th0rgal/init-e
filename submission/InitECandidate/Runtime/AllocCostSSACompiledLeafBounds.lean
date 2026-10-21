import InitECandidate.Runtime.AllocCostSSAStageCases
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordUnreach.Proofs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticIf
import InitECandidate.Runtime.AllocMoveTable
import InitECandidate.Runtime.WordRefinedLocalPrice
import InitECandidate.Runtime.WordStackRefinedLeaf
import InitECandidate.Runtime.WordOptimizerPrice

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

/-- **One currency on the same node.**  Composing finite-auth's `goSeq_move` with
`allocMovePrice_le` puts the certified schedule directly in terms of the physical
nonself count my charge is built from:
`12 * (parmove (physPairs pairs)).length <= 28 * nonselfCount pairs`. -/
theorem move_node_schedule_le {pri : Nat} {pairs : List (Nat × Nat)} {before : Nat}
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    12 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length ≤
      28 * nonselfCount pairs :=
  le_trans (goSeq_move ok) (allocMovePrice_le pairs)

/-- `allocMovePrice` in closed form over the physical nonself count. -/
theorem allocMovePrice_eq (pairs : List (Nat × Nat)) :
    allocMovePrice pairs =
      (if nonselfCount pairs ≤ 1 then 12 * nonselfCount pairs
        else 24 * nonselfCount pairs) := by
  unfold allocMovePrice
  dsimp only
  rw [physPairs_filter_length]

/-- **His price is dominated by my charge, sharply.**  12 or 24 per physical nonself
pair never exceeds my 14/28 per emitted pair: in the small branch the list holds at
most one nonself pair so the 14-per-pair charge covers 12, and otherwise 24 ≤ 28 on a
list at least as long as its nonself count. -/
theorem allocMovePrice_le_certifiedCharge (pairs : List (Nat × Nat)) :
    allocMovePrice pairs ≤ certifiedMoveCharge pairs := by
  rw [allocMovePrice_eq]
  unfold certifiedMoveCharge
  have h := nonselfCount_le pairs
  split <;> split <;> omega

/-- **The certificate charges at most my executed-cost charge, on the real node.**
Composing finite-auth's `goSeq_move` with the sharp dominance gives, for an actually
emitted move node,
`12 * (parmove (physPairs pairs)).length <= certifiedMoveCharge pairs`
- the schedule and the executed cost agree on the same pair list, with self moves
free and no target-run assumption. -/
theorem move_node_schedule_le_charge {pri : Nat} {pairs : List (Nat × Nat)}
    {before : Nat} (ok : (goSeq before (.move pri pairs)).1 = true) :
    12 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length ≤
      certifiedMoveCharge pairs :=
  le_trans (goSeq_move ok) (allocMovePrice_le_certifiedCharge pairs)

/-- **`seq` stage transfer with a certified per-site overhead.**  Composing the
two fall-through decompositions (`wec_seq_none_split`) gives the whole-`seq` transfer:
node-price overhead plus the two halves' transfers at the reached middle states.  The
source-side price carries the certified per-site SSA overhead `extraNode`; the target
side is never charged a supplied budget. -/
theorem seq_transfer_fallthrough {C F : Type}
    (s1 s2 : WordLangProgHOL (BitVec 64))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock source (evaluate s1 source) = (none, midS))
    (hT : fixClock target (evaluate s1 target) = (none, midT))
    {extraNode extra1 extra2 : Nat}
    (hnode : nativeWordPrice (.seq s1 s2) target ≤
      nativeWordPrice (.seq s1 s2) source + extraNode)
    (h1 : wordExecutionCost nativeWordPrice s1 target ≤
      wordExecutionCost nativeWordPrice s1 source + extra1)
    (h2 : wordExecutionCost nativeWordPrice s2 midT ≤
      wordExecutionCost nativeWordPrice s2 midS + extra2) :
    wordExecutionCost nativeWordPrice (.seq s1 s2) target ≤
      wordExecutionCost nativeWordPrice (.seq s1 s2) source +
        (extraNode + (extra1 + extra2)) := by
  rw [wec_seq_none_split s1 s2 target midT hT,
    wec_seq_none_split s1 s2 source midS hS]
  omega

#print axioms seq_transfer_fallthrough
#print axioms move_node_schedule_le_charge
#print axioms allocMovePrice_le_certifiedCharge
#print axioms allocMovePrice_eq
#print axioms move_node_schedule_le
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


/-- The escaping outcome of `seq`: when the first half does not fall through, the
second half is charged nothing on either side, so the transfer is the first half's
transfer plus the node-price overhead. Inserted move suffixes are not charged here. -/
theorem seq_transfer_escape {C F : Type}
    (s1 s2 : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (hS : (fixClock source (evaluate s1 source)).1 = none -> False)
    (hT : (fixClock target (evaluate s1 target)).1 = none -> False)
    (extraNode extra1 : Nat)
    (hnode : nativeWordPrice (.seq s1 s2) target <=
      nativeWordPrice (.seq s1 s2) source + extraNode)
    (h1 : wordExecutionCost nativeWordPrice s1 target <=
      wordExecutionCost nativeWordPrice s1 source + extra1) :
    wordExecutionCost nativeWordPrice (.seq s1 s2) target <=
      wordExecutionCost nativeWordPrice (.seq s1 s2) source + extraNode + extra1 := by
  rw [wec_seq_some_split s1 s2 target hT,
    wec_seq_some_split s1 s2 source hS]
  omega

#print axioms seq_transfer_escape

/-- `ite` stage transfer.  Both `ssaCcTrans` branches on the condition, so the run-side
shape is: the node costs its own price plus the selected branch's cost (that is the
`.ite` clause of the counter, instantiated at each side's own selection).  Given those
two branch selections and the branch transfer, the whole-`ite` transfer holds with the
certified node-price overhead on the source side only.  The selected branches `bS`,
`bT` are the compiled branches `(ssaCcTrans e2 ssa na lt).1` / `(ssaCcTrans e3 ssa na lt).1`
wrapped by the merge suffix `fixInconsistencies ...` that `ssaCcTrans_ite_shape` emits. -/
theorem ite_transfer_of_branch {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64))
    (bS bT : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (extraNode extra1 : Nat)
    (hdecS : wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) source =
      nativeWordPrice (.ite cmp r1 ri e2 e3) source +
        wordExecutionCost nativeWordPrice bS source)
    (hdecT : wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) target =
      nativeWordPrice (.ite cmp r1 ri e2 e3) target +
        wordExecutionCost nativeWordPrice bT target)
    (hnode : nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode)
    (hb : wordExecutionCost nativeWordPrice bT target <=
      wordExecutionCost nativeWordPrice bS source + extra1) :
    wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode + extra1 := by
  rw [hdecS, hdecT]
  omega

#print axioms ite_transfer_of_branch

/-- The `.ite` clause of the counter, taken branch `true`: the node costs its own price
plus the cost of `e2`.  The lookups return `WordLocW 64` (see
WordSem/Accessors.lean:173 and :293), which is the carrier `wordSemWordCmp` compares. -/
theorem wec_ite_true {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some true) :
    wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) s =
      nativeWordPrice (.ite cmp r1 ri e2 e3) s +
        wordExecutionCost nativeWordPrice e2 s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  simp only [hx, hy, hc]

/-- The `.ite` clause of the counter, taken branch `false`. -/
theorem wec_ite_false {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some false) :
    wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) s =
      nativeWordPrice (.ite cmp r1 ri e2 e3) s +
        wordExecutionCost nativeWordPrice e3 s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  simp only [hx, hy, hc]

#print axioms wec_ite_true
#print axioms wec_ite_false

/-- Closed `ite` transfer, taken branch `true`: only run facts about the two selections
plus the node-price and branch transfers.  No branch-cost premise, no target budget. -/
theorem ite_transfer_true {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar r1 source = some xS) (hyS : getVarImm ri source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar r1 target = some xT) (hyT : getVarImm ri target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (extraNode extra1 : Nat)
    (hnode : nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode)
    (hb : wordExecutionCost nativeWordPrice e2 target <=
      wordExecutionCost nativeWordPrice e2 source + extra1) :
    wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode + extra1 := by
  rw [wec_ite_true cmp r1 ri e2 e3 source xS yS hxS hyS hcS,
      wec_ite_true cmp r1 ri e2 e3 target xT yT hxT hyT hcT]
  omega

/-- Closed `ite` transfer, taken branch `false`. -/
theorem ite_transfer_false {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar r1 source = some xS) (hyS : getVarImm ri source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some false)
    (hxT : getVar r1 target = some xT) (hyT : getVarImm ri target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some false)
    (extraNode extra1 : Nat)
    (hnode : nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode)
    (hb : wordExecutionCost nativeWordPrice e3 target <=
      wordExecutionCost nativeWordPrice e3 source + extra1) :
    wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) target <=
      wordExecutionCost nativeWordPrice (.ite cmp r1 ri e2 e3) source + extraNode + extra1 := by
  rw [wec_ite_false cmp r1 ri e2 e3 source xS yS hxS hyS hcS,
      wec_ite_false cmp r1 ri e2 e3 target xT yT hxT hyT hcT]
  omega

#print axioms ite_transfer_true
#print axioms ite_transfer_false

/-- **Charge at the actual call-site argument move.**  Instantiating the composed
prefix charge at the very pair list the `.call` clause emits
(`convArgs.zip names` with `convArgs := (List.range names.length).map (fun x => 2*x)`,
SSACcTrans.lean:142-147): the inserted argument moves cost exactly
`certifiedMoveCharge` of that list, and the rest of the call site is charged where the
move actually reaches it. -/
theorem call_arg_prefix_charge {C F : Type} (ssa : Spt Nat) (args : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (hfix : fixClock s (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) s) = (none, mid)) :
    wordExecutionCost nativeWordPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
          fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) s =
      nativeWordPrice
        (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
          fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) s +
      certifiedMoveCharge (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa))) +
      wordExecutionCost nativeWordPrice tail mid :=
  wec_move_seq_charge 1 _ tail s mid hfix

#print axioms call_arg_prefix_charge

/-- Charge at the live-name stack move of a returning call.  By
`listNextVarRenameMove_shape` that node is `.move 0 ((listNextVarRename ls ssa n).1.zip
(ls.map (optionLookup ssa)))`, so charging it gives exactly `certifiedMoveCharge` of the
live-name list and the continuation at the reached state. -/
theorem stack_live_move_prefix_charge {C F : Type}
    (ssa : Spt Nat) (n : Nat) (ls : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (hfix : fixClock s (evaluate (.move 0
      ((listNextVarRename ls ssa n).1.zip (ls.map (optionLookup ssa)))) s) =
      (none, mid)) :
    wordExecutionCost nativeWordPrice
      (.seq (.move 0 ((listNextVarRename ls ssa n).1.zip
        (ls.map (optionLookup ssa)))) tail) s =
      nativeWordPrice
        (.seq (.move 0 ((listNextVarRename ls ssa n).1.zip
          (ls.map (optionLookup ssa)))) tail) s +
      certifiedMoveCharge ((listNextVarRename ls ssa n).1.zip
        (ls.map (optionLookup ssa))) +
      wordExecutionCost nativeWordPrice tail mid :=
  wec_move_seq_charge 0 _ tail s mid hfix

#print axioms stack_live_move_prefix_charge


/-- Price-generic move charge: a move node costs exactly its own price. -/
theorem wec_move_generic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price (.move pri moves) s = price (.move pri moves) s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip

/-- Price-generic fall-through split for `seq`. -/
theorem wec_seq_none_split_generic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (f g : WordLangProgHOL (BitVec 64)) (s mid : WordSemStateFiniteExact 64 C F)
    (h : fixClock s (evaluate f s) = (none, mid)) :
    wordExecutionCost price (.seq f g) s =
      price (.seq f g) s + wordExecutionCost price f s +
        wordExecutionCost price g mid := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  rw [h]

#print axioms wec_move_generic
#print axioms wec_seq_none_split_generic

/-- **`seq` composition at the canonical target price.**  Same shape as
`seq_transfer_fallthrough`, priced by the checked canonical `refinedWordLocalPrice`
instead of `nativeWordPrice`, via the price-generic splits.  Obligations: the node-price
overhead `extraNode` and the two halves' transfers at the reached middle states.  The
move term stays the price of the move node, to be filled by the checked scheduler-exact
leaf budget rather than by any 14/28 overestimate. -/
theorem seq_transfer_refined {C F : Type}
    (f g : WordLangProgHOL (BitVec 64))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock source (evaluate f source) = (none, midS))
    (hT : fixClock target (evaluate f target) = (none, midT))
    (extraNode extra1 extra2 : Nat)
    (hnode : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) target <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) source + extraNode)
    (h1 : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f source + extra1)
    (h2 : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice g midT <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice g midS + extra2) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) source
        + extraNode + extra1 + extra2 := by
  rw [wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) f g target midT hT,
      wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) f g source midS hS]
  omega

#print axioms seq_transfer_refined

/-- Price-generic `ite` decomposition, taken branch true. -/
theorem wec_ite_true_generic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some true) :
    wordExecutionCost price (.ite cmp r1 ri e2 e3) s =
      price (.ite cmp r1 ri e2 e3) s + wordExecutionCost price e2 s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  simp only [hx, hy, hc]

/-- Price-generic `ite` decomposition, taken branch false. -/
theorem wec_ite_false_generic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some false) :
    wordExecutionCost price (.ite cmp r1 ri e2 e3) s =
      price (.ite cmp r1 ri e2 e3) s + wordExecutionCost price e3 s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  simp only [hx, hy, hc]

#print axioms wec_ite_true_generic
#print axioms wec_ite_false_generic

/-- **`ite` composition at the canonical target price**, taken branch true.  Only run
facts about the two selections, the node-price overhead and the branch transfer; priced
by `refinedWordLocalPrice`, so the ite node's own canonical price (23 in its fallback
clause) carries the overhead and nothing is assumed about the target budget. -/
theorem ite_transfer_refined {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar r1 source = some xS) (hyS : getVarImm ri source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar r1 target = some xT) (hyT : getVarImm ri target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (extraNode extra1 : Nat)
    (hnode : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri e2 e3) target <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri e2 e3) source + extraNode)
    (hb : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice e2 target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice e2 source + extra1) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri e2 e3) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri e2 e3) source
        + extraNode + extra1 := by
  rw [wec_ite_true_generic (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice)
        cmp r1 ri e2 e3 source xS yS hxS hyS hcS,
      wec_ite_true_generic (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice)
        cmp r1 ri e2 e3 target xT yT hxT hyT hcT]
  omega

#print axioms ite_transfer_refined

/-- **Call-site argument move, priced canonically.**  The `.call` clause's inserted
argument move is charged at `refinedWordLocalPrice (.move 1 (convArgs.zip names)) s`, the
canonical price of exactly that node - the slot the checked scheduler-exact leaf budget
fills.  No 14/28 overestimate appears. -/
theorem call_arg_prefix_charge_refined {C F : Type} (ssa : Spt Nat) (args : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (hfix : fixClock s (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) s) = (none, mid)) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
          fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
          fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) s +
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
          fun x => 2 * x).zip (args.map (optionLookup ssa)))) s +
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice tail mid := by
  rw [wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) _ tail s mid hfix,
      wec_move_generic (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) 1 _ s]

/-- **Live-name stack move of a returning call, priced canonically.** -/
theorem stack_live_move_prefix_charge_refined {C F : Type}
    (ssa : Spt Nat) (n : Nat) (ls : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (hfix : fixClock s (evaluate (.move 0
      ((listNextVarRename ls ssa n).1.zip (ls.map (optionLookup ssa)))) s) = (none, mid)) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 0 ((listNextVarRename ls ssa n).1.zip
        (ls.map (optionLookup ssa)))) tail) s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq (.move 0 ((listNextVarRename ls ssa n).1.zip
          (ls.map (optionLookup ssa)))) tail) s +
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.move 0 ((listNextVarRename ls ssa n).1.zip
          (ls.map (optionLookup ssa)))) s +
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice tail mid := by
  rw [wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) _ tail s mid hfix,
      wec_move_generic (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) 0 _ s]

#print axioms call_arg_prefix_charge_refined
#print axioms stack_live_move_prefix_charge_refined

/-- **Whole call-site composition, canonically priced.**  Combines the inserted
argument-move prefix charge with the move's own price differential and the tail's
transfer at the reached middle states.  The move differential `hmove` is where the
scheduler-exact price of the emitted node enters: for a move node it is
`refinedWordLocalPrice (.move 1 pairs) target <= refinedWordLocalPrice (.move 1 pairs)
source + extra1`, i.e. exactly the obligation the checked table discharges. -/
theorem call_site_transfer_refined {C F : Type} (ssa : Spt Nat) (args : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock source (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) source) = (none, midS))
    (hT : fixClock target (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) target) = (none, midT))
    (extraNode extra1 extra2 : Nat)
    (hnode : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) target <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) source + extraNode)
    (hmove : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) target <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) source + extra1)
    (htail : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      tail midT <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      tail midS + extra2) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) source
        + extraNode + extra1 + extra2 := by
  rw [call_arg_prefix_charge_refined ssa args tail target midT hT,
      call_arg_prefix_charge_refined ssa args tail source midS hS]
  omega

#print axioms call_site_transfer_refined

/-- **The canonical price of a move node is the exact scheduler length.**  From root's
checked leaf table (WordStackRefinedLeaf.lean:15)
  refinedWordStackLeafBudget (.move _ moves)
    = some (12 * (Parmove.parmove (moves.map (fun m => (m.1/2, m.2/2)))).length),
so `refinedWordLocalPrice (.move pri pairss) s` is 12 times the physical scheduler length
- the exact number, not the legacy 14/28 per-pair overestimate. -/
theorem refinedWordLocalPrice_move (pri : Nat) (pairs : List (Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri pairs) s =
      12 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget, physPairs]
#print axioms refinedWordLocalPrice_move

/-- **The canonical price ignores the state.**  Its state argument is unused, so a
node's canonical price is the same on the source and the target run: every price
differential in the transfer is zero rather than an assumed budget. -/
theorem refinedWordLocalPrice_state_independent {C F : Type}
    (program : WordLangProgHOL (BitVec 64))
    (s t : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice program s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice program t := by
  unfold InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
  split <;> rfl

/-- Hence the emitted move node's canonical price differential is zero: the `extra1`
slot of the site composition is genuinely 0 for a move node. -/
theorem move_price_differential_zero {C F : Type} (pri : Nat) (pairs : List (Nat × Nat))
    (s t : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri pairs) t <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri pairs) s + 0 := by
  simpa using le_of_eq (refinedWordLocalPrice_state_independent
    (C := C) (F := F) (.move pri pairs) t s)

#print axioms refinedWordLocalPrice_state_independent
#print axioms move_price_differential_zero

/-- **Same site on both runs: only the tail's cost differs.**  Because the canonical
price is state-independent, a call site that appears identically on the source and the
target contributes no differential at all - neither the node price nor the canonical
price of the emitted move - so the transfer reduces to the tail's transfer at the
reached states.  This is the shape the table transfer needs: the source side pays only
for the nodes the allocator ADDS, not for the ones both runs share. -/
theorem call_site_transfer_no_differential {C F : Type} (ssa : Spt Nat) (args : List Nat)
    (tail : WordLangProgHOL (BitVec 64))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock source (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) source) = (none, midS))
    (hT : fixClock target (evaluate (.move 1
      (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) target) = (none, midT))
    (extra2 : Nat)
    (htail : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      tail midT <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        tail midS + extra2) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) source + extra2 := by
  rw [call_arg_prefix_charge_refined ssa args tail target midT hT,
      call_arg_prefix_charge_refined ssa args tail source midS hS]
  have hn : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) target =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) tail) source :=
    refinedWordLocalPrice_state_independent _ _ _
  have hm : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) target =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.move 1 (((List.range (args.map (optionLookup ssa)).length).map
        fun x => 2 * x).zip (args.map (optionLookup ssa)))) source :=
    refinedWordLocalPrice_state_independent _ _ _
  rw [hn, hm]
  omega

#print axioms call_site_transfer_no_differential

/-- **Any move-prefixed `seq` shared by both runs costs nothing in differential.**  A
move node costs exactly its own canonical price (`wec_move_generic`), and that price is
state-independent, so for a `.seq (.move pri pairs) tail` appearing identically on the
source and the target run the only remaining difference is the tail's cost at the reached
middle states.  This covers both inserted-move sites (call argument moves and the
returning-call live-name stack move) uniformly. -/
theorem move_seq_no_differential {C F : Type} (pri : Nat) (pairs : List (Nat × Nat))
    (tail : WordLangProgHOL (BitVec 64))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock source (evaluate (.move pri pairs) source) = (none, midS))
    (hT : fixClock target (evaluate (.move pri pairs) target) = (none, midT))
    (extra2 : Nat)
    (htail : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      tail midT <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        tail midS + extra2) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move pri pairs) tail) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq (.move pri pairs) tail) source + extra2 := by
  rw [wec_seq_none_split_generic _ (.move pri pairs) tail target midT hT,
      wec_seq_none_split_generic _ (.move pri pairs) tail source midS hS,
      wec_move_generic _ pri pairs target,
      wec_move_generic _ pri pairs source]
  have hn : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq (.move pri pairs) tail) target =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq (.move pri pairs) tail) source :=
    refinedWordLocalPrice_state_independent _ _ _
  have hm : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.move pri pairs) target =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.move pri pairs) source :=
    refinedWordLocalPrice_state_independent _ _ _
  rw [hn, hm]
  omega

#print axioms move_seq_no_differential

/-- **The scheduler certificate bounds the canonical move price itself.**  With
`refinedWordLocalPrice_move` the canonical price of a move node IS
`12 * (parmove (physPairs pairs)).length`, so finite-auth's `goSeq_move` bounds it directly:

  refinedWordLocalPrice (.move pri pairs) s <= allocMovePrice pairs

whenever the table accepts that node.  This is the point where the coalescing table enters
the transfer: it bounds exactly the quantity the source side is charged for an inserted move,
in the canonical currency, with no 14/28 and no target budget. -/
theorem canonical_move_price_le_table {C F : Type} (pri : Nat) (pairs : List (Nat × Nat))
    (before : Nat) (s : WordSemStateFiniteExact 64 C F)
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri pairs) s <=
      allocMovePrice pairs := by
  rw [refinedWordLocalPrice_move]
  exact goSeq_move ok

/-- And the table price is itself dominated by the calibrated physical count, so the
canonical price is bounded by a function of `nonselfCount` alone: self moves cost nothing. -/
theorem canonical_move_price_le_nonself {C F : Type} (pri : Nat) (pairs : List (Nat × Nat))
    (before : Nat) (s : WordSemStateFiniteExact 64 C F)
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri pairs) s <=
      28 * nonselfCount pairs := by
  refine le_trans (canonical_move_price_le_table pri pairs before s ok) (allocMovePrice_le pairs)

#print axioms canonical_move_price_le_table
#print axioms canonical_move_price_le_nonself


/-- Price-generic escaping split for `seq`: when the first half does not fall through,
the second half is charged nothing. -/
theorem wec_seq_some_split_generic {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (f g : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (h : (fixClock s (evaluate f s)).1 = none → False) :
    wordExecutionCost price (.seq f g) s =
      price (.seq f g) s + wordExecutionCost price f s := by
  rw [wordExecutionCost]
  all_goals first | rfl | (intros; contradiction) | skip
  generalize hfix : fixClock s (evaluate f s) = pair at h ⊢
  obtain ⟨res, mid⟩ := pair
  simp only [Prod.fst, Prod.snd] at h ⊢
  cases res with
  | none => exact absurd rfl h
  | some r => simp only [Nat.add_zero]

/-- **`seq` escape composition at the canonical target price.**  The dual of
`seq_transfer_refined`: when the first half escapes, the second half is charged nothing
on either side, so the transfer is the first half's transfer plus the node-price
overhead, at `refinedWordLocalPrice`. -/
theorem seq_transfer_escape_refined {C F : Type}
    (f g : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (hS : (fixClock source (evaluate f source)).1 = none → False)
    (hT : (fixClock target (evaluate f target)).1 = none → False)
    (extraNode extra1 : Nat)
    (hnode : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq f g) target <=
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) source + extraNode)
    (h1 : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      f target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        f source + extra1) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq f g) target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq f g) source + extraNode + extra1 := by
  rw [wec_seq_some_split_generic _ f g target hT,
      wec_seq_some_split_generic _ f g source hS]
  omega

#print axioms wec_seq_some_split_generic
#print axioms seq_transfer_escape_refined

/-- `refinedWordLocalPrice` of a `seq` node is zero: the leaf table has no entry for it
and the fallback lists only ite/loop/call. -/
theorem refinedWordLocalPrice_seq_zero {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) s = 0 := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget]

/-- **The `ssaCcTrans` `seq` constructor, COMPILED syntax on the left.**  The target run is
the compiled program `(ssaCcTrans (.seq first second) ssa next tables).1`, whose shape is
`.seq firstOut secondOut` with `firstOut := (ssaCcTrans first ssa next tables).1` and
`secondOut := (ssaCcTrans second (ssaCcTrans first ssa next tables).2.1
(ssaCcTrans first ssa next tables).2.2 tables).1` (ssaCcTrans_seq_shape).  The two IHs are
the actual first/second compiled bodies against their source bodies, and the reached pair
is split on the compiled first body for the target and on the source first body for the
source.  Conclusion: the compiled seq's executed cost is at most the source seq's cost plus
the two body transfers; the seq node itself contributes nothing (its canonical price is 0 on
both sides). -/
theorem ssaCcTrans_seq_transfer_compiled {C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target midS midT : WordSemStateFiniteExact 64 C F)
    (extra1 extra2 : Nat)
    (hS : fixClock source (evaluate first source) = (none, midS))
    (hT : fixClock target
      (evaluate ((ssaCcTrans first ssa next tables)).1 target) = (none, midT))
    (h1 : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      ((ssaCcTrans first ssa next tables)).1 target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        first source + extra1)
    (h2 : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      ((ssaCcTrans second ((ssaCcTrans first ssa next tables)).2.1
        ((ssaCcTrans first ssa next tables)).2.2 tables)).1 midT <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        second midS + extra2) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      ((ssaCcTrans (.seq first second) ssa next tables)).1 target <=
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
        (.seq first second) source + extra1 + extra2 := by
  rw [ssaCcTrans_seq_shape]
  rw [wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) _ _ target midT hT,
      wec_seq_none_split_generic
        (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice) _ _ source midS hS]
  have hp1 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq ((ssaCcTrans first ssa next tables)).1
        ((ssaCcTrans second ((ssaCcTrans first ssa next tables)).2.1
          ((ssaCcTrans first ssa next tables)).2.2 tables)).1) target = 0 :=
    refinedWordLocalPrice_seq_zero _ _ _
  have hp2 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.seq first second) source = 0 := refinedWordLocalPrice_seq_zero _ _ _
  rw [hp1, hp2]
  omega

#print axioms refinedWordLocalPrice_seq_zero
#print axioms ssaCcTrans_seq_transfer_compiled

/-! ## Quantitative SSA simulation (plain-state runs)

The runs are exposed at the PLAIN states.  A `permute`-indexed run cannot be composed for
`seq`: the evaluator mutates the `permute` field during a run (inst_withPermute,
wordSemEnvToList ... s.permute), so the composite run's final state carries the second body's
permutation while its initial state can only carry one chosen permutation.  The compiler's
simulation conjunct keeps the permutation, where it belongs. -/
noncomputable def quantSsaSimulation {C F : Type}
    (prog : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) (extra : Nat) : Prop :=
  ssaSimulation prog source target ssa next tables ∧
  (∃ rS : Option (WordSemResult 64), ∃ sS : WordSemStateFiniteExact 64 C F, ∃ rT : Option (WordSemResult 64), ∃ sT : WordSemStateFiniteExact 64 C F,
    WordSemStateFiniteExact.evaluate prog source = (rS, sS) ∧
    WordSemStateFiniteExact.evaluate ((ssaCcTrans prog ssa next tables).1) target = (rT, sT) ∧
    rS = rT) ∧
  wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice ((ssaCcTrans prog ssa next tables).1) target ≤
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice prog source + extra

theorem quantSsaSimulation.toSsaSimulation {C F : Type}
    (prog : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) (extra : Nat)
    (h : quantSsaSimulation (C := C) (F := F) prog source target ssa next tables extra) :
    ssaSimulation prog source target ssa next tables :=
  h.1


/-! ## Restored supporting lemmas (see the commits referenced in the log) -/

theorem refinedWordLocalPrice_ite {C F : Type} (op : Cmp) (condition : Nat)
    (right : WordRegImm (BitVec 64))
    (thenBranch elseBranch : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.ite op condition right thenBranch elseBranch) s = 23 := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget]

theorem refinedWordLocalPrice_loop {C F : Type}
    (liveIn : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (liveOut : WordLangNumSetHOL) (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop liveIn body liveOut) s = 2 := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget]

theorem refinedWordLocalPrice_call_none {C F : Type}
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none target arguments handler) s = 41 := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget]

theorem evaluate_seq_none {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (h : fixClock s (WordSemStateFiniteExact.evaluate c1 s) = (none, mid)) :
    WordSemStateFiniteExact.evaluate (.seq c1 c2) s =
      WordSemStateFiniteExact.evaluate c2 mid := by
  simp only [WordSemStateFiniteExact.evaluate, h]

theorem evaluate_seq_escape {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec 64))
    (s mid : WordSemStateFiniteExact 64 C F)
    (res : Option (WordSemResult 64))
    (h : fixClock s (WordSemStateFiniteExact.evaluate c1 s) = (res, mid))
    (hr : res = none → False) :
    WordSemStateFiniteExact.evaluate (.seq c1 c2) s = (res, mid) := by
  simp only [WordSemStateFiniteExact.evaluate, h]

theorem fixClock_fst {C F : Type}
    (s : WordSemStateFiniteExact 64 C F)
    (p : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F) :
    (fixClock s p).1 = p.1 := by
  simp only [fixClock]

theorem fixClock_fst_none {C F : Type}
    (s : WordSemStateFiniteExact 64 C F)
    (p : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (h : p.1 = none) : (fixClock s p).1 = none := by
  rw [fixClock_fst, h]

def fixClockMid {C F : Type}
    (s : WordSemStateFiniteExact 64 C F)
    (p : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F) :
    WordSemStateFiniteExact 64 C F :=
  (fixClock s p).2

theorem getVar_permute {C F : Type} (name : Nat)
    (s : WordSemStateFiniteExact 64 C F) (perm : Nat → Nat → Nat) :
    getVar name {s with permute := perm} = getVar name s := rfl

/-- **The `seq` constructor, fall-through outcome.**  From the two recursive quantitative IHs
(the second instantiated at the reached middle and at the threaded allocator state) this
DERIVES the composite runs, the composite simulation and the composite cost: `midS`/`midT` are
the `fixClock`ed reached states, the first body's outcome is read from the evaluator, and the
second body supplies the final runs.  No final run or cost is assumed. -/
theorem ssaCcTrans_seq_quant_none {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (extra1 extra2 : Nat)
    (firstIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation second source target ssa next tables)
    (hinv : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.seq first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables)
    (h1 : quantSsaSimulation (C := C) (F := F) first source target ssa next tables extra1)
    (h2 : ∀ (src tgt : WordSemStateFiniteExact 64 C F) (s2 : Spt Nat) (n2 : Nat),
      quantSsaSimulation (C := C) (F := F) second src tgt s2 n2 tables extra2)
    (hS0 : (WordSemStateFiniteExact.evaluate first source).1 = none) :
    quantSsaSimulation (C := C) (F := F) (.seq first second) source target ssa next tables
      (extra1 + extra2) := by
  obtain ⟨hsim1, ⟨rS1, sS1, rT1, sT1, hrunS1, hrunT1, hout1⟩, hcost1⟩ := h1
  have hr1 : rS1 = none := by
    have hs := hS0
    rw [hrunS1] at hs
    exact hs
  have hrT1 : (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target).1 = none := by
    rw [hrunT1, ← hout1, hr1]
  set midS := (fixClock source (WordSemStateFiniteExact.evaluate first source)).2 with hmidS
  set midT := (fixClock target (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target)).2 with hmidT
  have hS : fixClock source (WordSemStateFiniteExact.evaluate first source) = (none, midS) := by
    simp only [hmidS, fixClock, hS0]
  have hT : fixClock target (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target) = (none, midT) := by
    simp only [hmidT, fixClock, hrT1]
  obtain ⟨hsim2, ⟨rS2, sS2, rT2, sT2, hrunS2, hrunT2, hout2⟩, hcost2⟩ :=
    h2 midS midT (ssaCcTrans first ssa next tables).2.1 (ssaCcTrans first ssa next tables).2.2
  refine ⟨ssaCcTransCorrectSeq first second source target ssa next tables firstIH secondIH hinv,
    ⟨rS2, sS2, rT2, sT2, ?_, ?_, hout2⟩, ?_⟩
  · rw [evaluate_seq_none first second source midS hS, hrunS2]
  · rw [ssaCcTrans_seq_shape, evaluate_seq_none (ssaCcTrans first ssa next tables).1 (ssaCcTrans second (ssaCcTrans first ssa next tables).2.1 (ssaCcTrans first ssa next tables).2.2 tables).1 target midT hT, hrunT2]
  · rw [ssaCcTrans_seq_shape,
      wec_seq_none_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice _ _ target midT hT,
      wec_seq_none_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice _ _ source midS hS]
    have hp1 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq (ssaCcTrans first ssa next tables).1 (ssaCcTrans second (ssaCcTrans first ssa next tables).2.1 (ssaCcTrans first ssa next tables).2.2 tables).1) target = 0 :=
      refinedWordLocalPrice_seq_zero _ _ _
    have hp2 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq first second) source = 0 :=
      refinedWordLocalPrice_seq_zero _ _ _
    rw [hp1, hp2]
    omega

#print axioms ssaCcTrans_seq_quant_none


/-- **The `seq` constructor, escape outcome.**  When the first body does not fall through the
second body never runs: the composite run is the first body's reached pair on both sides, and
the cost is the first body's cost plus the (zero) `seq` node price.  The first body's run and
cost come from its quantitative IH; the outcome is read off the evaluator. -/
theorem ssaCcTrans_seq_quant_escape {C F : Type}
    (first second : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (extra1 extra2 : Nat)
    (firstIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation second source target ssa next tables)
    (hinv : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.seq first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables)
    (h1 : quantSsaSimulation (C := C) (F := F) first source target ssa next tables extra1)
    (hS0 : (WordSemStateFiniteExact.evaluate first source).1 = none → False) :
    quantSsaSimulation (C := C) (F := F) (.seq first second) source target ssa next tables
      (extra1 + extra2) := by
  obtain ⟨hsim1, ⟨rS1, sS1, rT1, sT1, hrunS1, hrunT1, hout1⟩, hcost1⟩ := h1
  have hr1 : rS1 ≠ none := by
    intro h
    apply hS0
    rw [hrunS1]
    exact h
  have hrT1 : rT1 ≠ none := by
    intro h
    exact hr1 (hout1 ▸ h)
  set midS := (fixClock source (WordSemStateFiniteExact.evaluate first source)).2 with hmidS
  set midT := (fixClock target (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target)).2 with hmidT
  have hS : fixClock source (WordSemStateFiniteExact.evaluate first source) = (rS1, midS) := by
    simp only [hmidS, hrunS1, fixClock]
  have hT : fixClock target (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target) = (rT1, midT) := by
    simp only [hmidT, hrunT1, fixClock]
  have hsSome : (fixClock source (WordSemStateFiniteExact.evaluate first source)).1 = none → False := by
    intro h
    rw [hS] at h
    exact hr1 h
  have htSome : (fixClock target (WordSemStateFiniteExact.evaluate (ssaCcTrans first ssa next tables).1 target)).1 = none → False := by
    intro h
    rw [hT] at h
    exact hrT1 h
  refine ⟨ssaCcTransCorrectSeq first second source target ssa next tables firstIH secondIH hinv,
    ⟨rS1, midS, rT1, midT, ?_, ?_, hout1⟩, ?_⟩
  · rw [evaluate_seq_escape first second source midS rS1 hS hr1]
  · rw [ssaCcTrans_seq_shape, evaluate_seq_escape (ssaCcTrans first ssa next tables).1 (ssaCcTrans second (ssaCcTrans first ssa next tables).2.1 (ssaCcTrans first ssa next tables).2.2 tables).1 target midT rT1 hT hrT1]
  · rw [ssaCcTrans_seq_shape,
      wec_seq_some_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice _ _ target htSome,
      wec_seq_some_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice _ _ source hsSome]
    have hp1 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq (ssaCcTrans first ssa next tables).1 (ssaCcTrans second (ssaCcTrans first ssa next tables).2.1 (ssaCcTrans first ssa next tables).2.2 tables).1) target = 0 :=
      refinedWordLocalPrice_seq_zero _ _ _
    have hp2 : InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq first second) source = 0 :=
      refinedWordLocalPrice_seq_zero _ _ _
    rw [hp1, hp2]
    omega

#print axioms ssaCcTrans_seq_quant_escape

/-! ## The evaluator's `ite` clause

`evaluate` (Evaluate.lean:184) selects a branch directly from the comparison - there is no
`fixClock` step, matching the counter's `.ite` clause.  These expose which branch ran, which is
what the ite induction case needs to DERIVE its run instead of assuming it. -/
theorem evaluate_ite_true {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (c1 c2 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some true) :
    WordSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2) s =
      WordSemStateFiniteExact.evaluate c1 s := by
  simp only [WordSemStateFiniteExact.evaluate, hx, hy, hc]

theorem evaluate_ite_false {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (c1 c2 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some false) :
    WordSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2) s =
      WordSemStateFiniteExact.evaluate c2 s := by
  simp only [WordSemStateFiniteExact.evaluate, hx, hy, hc]

/-- The `ite` node's cost is its canonical price plus the selected branch's cost, on both sides. -/
theorem wec_ite_true_canonical {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (c1 c2 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (x y : WordLocW 64)
    (hx : getVar r1 s = some x) (hy : getVarImm ri s = some y)
    (hc : wordSemWordCmp cmp x y = some true) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice
      (.ite cmp r1 ri c1 c2) s =
      23 + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice c1 s := by
  rw [wordExecutionCost]
  simp only [hx, hy, hc, refinedWordLocalPrice_ite]

#print axioms evaluate_ite_true
#print axioms evaluate_ite_false
#print axioms wec_ite_true_canonical
/-- `ite` cost transfer, then-branch: the node price 23 is the same on both sides (it is a
constant of the program, and `refinedWordLocalPrice` is state independent), so the transfer
reduces to the selected branch's cost transfer. -/
theorem ite_transfer_then_canonical {C F : Type}
    (cmp : Cmp) (r1 r1' : Nat) (ri ri' : WordRegImm (BitVec 64))
    (c1 c2 c1' c2' : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar r1 source = some xS) (hyS : getVarImm ri source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar r1' target = some xT) (hyT : getVarImm ri' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (extra : Nat)
    (hb : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice c1' target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice c1 source + extra) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1' ri' c1' c2') target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri c1 c2) source + extra := by
  rw [wec_ite_true_canonical cmp r1' ri' c1' c2' target xT yT hxT hyT hcT,
      wec_ite_true_canonical cmp r1 ri c1 c2 source xS yS hxS hyS hcS]
  omega

/-- The same for the else-branch. -/
theorem ite_transfer_else_canonical {C F : Type}
    (cmp : Cmp) (r1 r1' : Nat) (ri ri' : WordRegImm (BitVec 64))
    (c1 c2 c1' c2' : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar r1 source = some xS) (hyS : getVarImm ri source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some false)
    (hxT : getVar r1' target = some xT) (hyT : getVarImm ri' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some false)
    (extra : Nat)
    (hb : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice c2' target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice c2 source + extra) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1' ri' c1' c2') target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp r1 ri c1 c2) source + extra := by
  rw [wordExecutionCost, wordExecutionCost]
  simp only [hxT, hyT, hcT, hxS, hyS, hcS, refinedWordLocalPrice_ite]
  omega

#print axioms ite_transfer_then_canonical
#print axioms ite_transfer_else_canonical
/-- `ite` stage (then branch): both runs and the counter bound in one package.  The source
and the compiled ite are compared with their own (possibly renamed) condition registers;
when both select the same branch, the runs are that branch's runs and the cost transfer
is the branch's transfer - the 23 node price cancels because it is the same on both sides. -/
theorem ite_stage_then {C F : Type}
    (cmp : Cmp) (left left' : Nat)
    (immediate immediate' : WordRegImm (BitVec 64))
    (first second thenT elseT : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (xS yS xT yT : WordLocW 64)
    (hxS : getVar left source = some xS) (hyS : getVarImm immediate source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar left' target = some xT) (hyT : getVarImm immediate' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (extra : Nat)
    (hb : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice thenT target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice first source + extra) :
    WordSemStateFiniteExact.evaluate (.ite cmp left immediate first second) source = WordSemStateFiniteExact.evaluate first source ∧
    WordSemStateFiniteExact.evaluate (.ite cmp left' immediate' thenT elseT) target = WordSemStateFiniteExact.evaluate thenT target ∧
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp left' immediate' thenT elseT) target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp left immediate first second) source + extra := ⟨
  evaluate_ite_true cmp left immediate first second source xS yS hxS hyS hcS,
  evaluate_ite_true cmp left' immediate' thenT elseT target xT yT hxT hyT hcT,
  ite_transfer_then_canonical cmp left left' immediate immediate' first second thenT elseT
    source target xS yS xT yT hxS hyS hcS hxT hyT hcT extra hb⟩

/-- `ite` stage (else branch): both runs and the counter bound in one package.  The source
and the compiled ite are compared with their own (possibly renamed) condition registers;
when both select the same branch, the runs are that branch's runs and the cost transfer
is the branch's transfer - the 23 node price cancels because it is the same on both sides. -/
theorem ite_stage_else {C F : Type}
    (cmp : Cmp) (left left' : Nat)
    (immediate immediate' : WordRegImm (BitVec 64))
    (first second thenT elseT : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (xS yS xT yT : WordLocW 64)
    (hxS : getVar left source = some xS) (hyS : getVarImm immediate source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some false)
    (hxT : getVar left' target = some xT) (hyT : getVarImm immediate' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some false)
    (extra : Nat)
    (hb : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice elseT target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice second source + extra) :
    WordSemStateFiniteExact.evaluate (.ite cmp left immediate first second) source = WordSemStateFiniteExact.evaluate second source ∧
    WordSemStateFiniteExact.evaluate (.ite cmp left' immediate' thenT elseT) target = WordSemStateFiniteExact.evaluate elseT target ∧
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp left' immediate' thenT elseT) target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.ite cmp left immediate first second) source + extra := ⟨
  evaluate_ite_false cmp left immediate first second source xS yS hxS hyS hcS,
  evaluate_ite_false cmp left' immediate' thenT elseT target xT yT hxT hyT hcT,
  ite_transfer_else_canonical cmp left left' immediate immediate' first second thenT elseT
    source target xS yS xT yT hxS hyS hcS hxT hyT hcT extra hb⟩

#print axioms ite_stage_then
#print axioms ite_stage_else
/-! ## Program-parametric quantitative transfer

`quantSsaSimulation` ties the cost to the compiler's own output, which is right for the whole
program but too rigid for a constructor whose compiled branch is `body ++ allocator-suffix`:
there the source program is the source BODY while the compiled program is the body's
compilation followed by the suffix.  `quantTransfer` therefore takes the compiled program as an
explicit parameter, so a constructor can be composed from branch transfers. -/
noncomputable def quantTransfer {C F : Type}
    (prog compiledProg : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat) : Prop :=
  (∃ rS : Option (WordSemResult 64), ∃ sS : WordSemStateFiniteExact 64 C F, ∃ rT : Option (WordSemResult 64), ∃ sT : WordSemStateFiniteExact 64 C F,
    WordSemStateFiniteExact.evaluate prog source = (rS, sS) ∧
    WordSemStateFiniteExact.evaluate compiledProg target = (rT, sT) ∧
    rS = rT) ∧
  wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice compiledProg target ≤
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice prog source + extra

/-- **ite composition** in the program-parametric language: when both ites select the then
branch, the transfer of the compiled branch against the source branch yields the transfer of
the compiled ite against the source ite.  The branch transfer is the recursive IH, and it is
where the compiled branch's allocator suffix (if any) is accounted for. -/
theorem ite_quantTransfer_then {C F : Type}
    (cmp : Cmp) (left left' : Nat)
    (immediate immediate' : WordRegImm (BitVec 64))
    (first second thenB elseB : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar left source = some xS) (hyS : getVarImm immediate source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar left' target = some xT) (hyT : getVarImm immediate' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (hbr : quantTransfer (C := C) (F := F) first thenB source target extra) :
    quantTransfer (C := C) (F := F) (.ite cmp left immediate first second)
      (.ite cmp left' immediate' thenB elseB) source target extra := by
  obtain ⟨⟨rS, sS, rT, sT, hrunS, hrunT, hout⟩, hcost⟩ := hbr
  refine ⟨⟨rS, sS, rT, sT, ?_, ?_, hout⟩, ?_⟩
  · rw [evaluate_ite_true cmp left immediate first second source xS yS hxS hyS hcS, hrunS]
  · rw [evaluate_ite_true cmp left' immediate' thenB elseB target xT yT hxT hyT hcT, hrunT]
  · exact ite_transfer_then_canonical cmp left left' immediate immediate' first second
      thenB elseB source target xS yS xT yT hxS hyS hcS hxT hyT hcT extra hcost

#print axioms ite_quantTransfer_then
/-! ## State independence of the allocator-only node costs

The allocator's own code (the move nodes and the inconsistency-fixing suffixes) must be
chargeable without knowing the state it runs in.  `refinedWordLocalPrice` is state independent
already, so a `.move` node's cost is a constant: this is the first half of the suffix fact. -/
theorem wec_move_state_independent {C F : Type} (pri : Nat) (moves : List (Nat × Nat))
    (s1 s2 : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri moves) s1 =
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.move pri moves) s2 := by
  rw [wec_move_generic, wec_move_generic, refinedWordLocalPrice_move,
      refinedWordLocalPrice_move]

#print axioms wec_move_state_independent
theorem wec_skip_state_independent {C F : Type} (s1 s2 : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice .skip s1 =
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice .skip s2 := by
  rw [wec_skip, wec_skip, refinedWordLocalPrice_state_independent]

#print axioms wec_skip_state_independent
/-- **`seq` composition of state independence.**  If both halves have state-independent costs and
the first half always falls through, the `seq` node's cost is state independent too: the seq's
own price is 0 (refinedWordLocalPrice_seq_zero) and the second half is charged at whatever middle
state each run reaches, where its cost is the same by hypothesis.  The fall-through hypothesis is
not decoration: without it a first half that escapes on one state and falls through on another
changes whether the second half is charged at all, and the costs genuinely differ.  For
allocator code the fall-through property is exactly what finite-auth's move table certifies. -/
theorem wec_seq_state_independent {C F : Type}
    (f g : WordLangProgHOL (BitVec 64))
    (hf : ∀ (s t : WordSemStateFiniteExact 64 C F), wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f s = wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f t)
    (hg : ∀ (s t : WordSemStateFiniteExact 64 C F), wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice g s = wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice g t)
    (hfall : ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate f s)).1 = none)
    (s1 s2 : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) s1 =
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq f g) s2 := by
  cases h1 : fixClock s1 (WordSemStateFiniteExact.evaluate f s1) with
  | mk r1 m1 =>
    cases h2 : fixClock s2 (WordSemStateFiniteExact.evaluate f s2) with
    | mk r2 m2 =>
      have hr1 : r1 = none := by simpa [h1] using hfall s1
      have hr2 : r2 = none := by simpa [h2] using hfall s2
      subst hr1
      subst hr2
      rw [wec_seq_none_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f g s1 m1 h1,
          wec_seq_none_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice f g s2 m2 h2,
          refinedWordLocalPrice_seq_zero f g s1,
          refinedWordLocalPrice_seq_zero f g s2,
          hf s1 s2, hg m1 m2]

#print axioms wec_seq_state_independent
/-- The canonical price of a returning `call` (root's fallback clause): the site charge plus the
spill charges for the arguments and results beyond the 22 registers the calling convention
keeps free. -/
theorem refinedWordLocalPrice_call_some {C F : Type}
    (values : List Nat) (cutsets : WordLangCutsetsHOL)
    (body : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call (some (values, cutsets, body, l1, l2)) target arguments handler) s =
      (if handler.isSome then 189 else 63) +
        39 * (arguments.length + 1 - 22) + 21 * (values.length + 1 - 22) := by
  simp only [InitECandidate.Runtime.WordToStack.refinedWordLocalPrice,
    InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget]

#print axioms refinedWordLocalPrice_call_some
/-! ## The call node's failure paths charge only the node price

`wordExecutionCost`'s `.call` clause (WordExecutionCost.lean:44) charges `price p s` whenever the
argument registers are not all present, the destination/argument list is invalid, or the code
lookup fails.  Those are exactly the paths the transfer must charge as a flat 41, so they are
isolated here. -/
theorem wec_call_none_getVars_none {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F)
    (hgv : getVars args s = none) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args handler) s = 41 := by
  rw [wordExecutionCost]
  simp only [hgv, refinedWordLocalPrice_call_none]

theorem wec_call_none_badDest {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64))
    (hgv : getVars args s = some xs)
    (hbad : wordSemBadDestArgs dest args = true) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args handler) s = 41 := by
  simp [wordExecutionCost, hgv, hbad, refinedWordLocalPrice_call_none]

#print axioms wec_call_none_getVars_none
#print axioms wec_call_none_badDest
/-! ## Fall-through of allocator code, from the two ingredients the invariants supply

A move node escapes exactly when its move list is not Nodup (a PROGRAM property) or one of its
source registers is missing (a STATE property, `getVars ... = none`).  Neither is a table
property: the first is syntactic, the second is what `ssaLocalsRel`/`ssaMapOK`/`everyVarHOL`
provide.  These lemmas turn those two into the fall-through hypothesis that
`wec_seq_state_independent` needs. -/
theorem move_fallthrough {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact 64 C F)
    (hnodup : (moves.map Prod.fst).Nodup)
    (hget : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none) :
    (fixClock s (WordSemStateFiniteExact.evaluate (.move pri moves) s)).1 = none := by
  rw [evaluate_move_none pri moves s hnodup hget]
  simp only [fixClock]

/-- Fall-through composes over `seq`: if both halves fall through from any state, so does their
sequence.  Proved the same way evaluate_seq_none was - by unfolding the evaluator's seq clause
with the reached fixClock split in hand. -/
theorem seq_fallthrough {C F : Type} (f g : WordLangProgHOL (BitVec 64))
    (hf : ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate f s)).1 = none)
    (hg : ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate g s)).1 = none)
    (s : WordSemStateFiniteExact 64 C F) :
    (fixClock s (WordSemStateFiniteExact.evaluate (.seq f g) s)).1 = none := by
  cases hfix : fixClock s (WordSemStateFiniteExact.evaluate f s) with
  | mk res mid =>
    have hres : res = none := by
      have h := hf s
      rw [hfix] at h
      exact h
    subst hres
    have hseq : WordSemStateFiniteExact.evaluate (.seq f g) s = WordSemStateFiniteExact.evaluate g mid := by
      simp only [WordSemStateFiniteExact.evaluate, hfix]
    rw [hseq, fixClock_fst]
    have hg' := hg mid
    rwa [fixClock_fst] at hg'

#print axioms seq_fallthrough
/-! ## The suffix's shape, charged

`fixInconsistencies` returns its branch suffix as `.seq (.move (priority prio true) lmov) lseq`
(SSAFixInconsistencies.lean:71).  This is that shape's cost: state independent, from the move
node's state-independent price, its certified fall-through (Nodup + all sources present), and the
same two facts for the remainder. -/
theorem suffix_seq_cost_independent {C F : Type}
    (prio : Nat) (moves : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec 64))
    (hnodup : (moves.map Prod.fst).Nodup)
    (hget : ∀ (s : WordSemStateFiniteExact 64 C F), WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none)
    (hrest_cost : ∀ (s t : WordSemStateFiniteExact 64 C F),
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice rest s = wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice rest t)
    (hrest_fall : ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate rest s)).1 = none)
    (s1 s2 : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq (.move prio moves) rest) s1 =
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.seq (.move prio moves) rest) s2 := by
  refine wec_seq_state_independent (.move prio moves) rest
    (wec_move_state_independent prio moves) hrest_cost ?_ s1 s2
  intro s
  exact move_fallthrough prio moves s hnodup (hget s)

#print axioms suffix_seq_cost_independent
/-! ## Allocator-only programs

`fakeMoves` builds its output by nesting: the empty case is `.skip`, each variable prepends
`.seq seqL (.move ...)` (SSAFixInconsistencies.lean:46-57).  Every inconsistency-fixing suffix is
therefore a tree of `seq` over move and skip leaves, and both properties the cost transfer needs
- fall-through and state-independent cost - are preserved by that tree. -/
inductive AllocOnly : WordLangProgHOL (BitVec 64) → Prop
  | skip : AllocOnly .skip
  | move : ∀ (pri : Nat) (moves : List (Nat × Nat)), AllocOnly (.move pri moves)
  | inst : ∀ (i : WordLangInst (BitVec 64)), AllocOnly (.inst i)
  | seq : ∀ (f g : WordLangProgHOL (BitVec 64)), AllocOnly f → AllocOnly g → AllocOnly (.seq f g)

theorem allocOnly_fallthrough {C F : Type}
    (hwf : ∀ (pri : Nat) (moves : List (Nat × Nat)),
      (moves.map Prod.fst).Nodup ∧ ∀ (s : WordSemStateFiniteExact 64 C F), WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none)
    (hinst : ∀ (i : WordLangInst (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      (fixClock s (WordSemStateFiniteExact.evaluate (.inst i) s)).1 = none)
    (p : WordLangProgHOL (BitVec 64)) (hp : AllocOnly p) :
    ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate p s)).1 = none := by
  induction hp with
  | skip =>
    intro s
    simp only [WordSemStateFiniteExact.evaluate, fixClock]
  | move pri moves =>
    intro s
    have hn : (moves.map Prod.fst).Nodup := (hwf pri moves).1
    have hg : WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none := (hwf pri moves).2 s
    exact move_fallthrough pri moves s hn hg
  | inst i =>
    intro s
    exact hinst i s
  | seq f g _ _ ihf ihg =>
    exact seq_fallthrough f g ihf ihg

theorem allocOnly_cost_independent {C F : Type}
    (hwf : ∀ (pri : Nat) (moves : List (Nat × Nat)),
      (moves.map Prod.fst).Nodup ∧ ∀ (s : WordSemStateFiniteExact 64 C F), WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none)
    (hinst : ∀ (i : WordLangInst (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      (fixClock s (WordSemStateFiniteExact.evaluate (.inst i) s)).1 = none)
    (p : WordLangProgHOL (BitVec 64)) (hp : AllocOnly p) :
    ∀ (s t : WordSemStateFiniteExact 64 C F), wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice p s = wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice p t := by
  induction hp with
  | skip =>
    intro s t
    exact wec_skip_state_independent s t
  | move pri moves =>
    intro s t
    exact wec_move_state_independent pri moves s t
  | inst i =>
    intro s t
    rw [wec_inst, wec_inst, refinedWordLocalPrice_state_independent]
  | seq f g hf hg ihf ihg =>
    intro s t
    exact wec_seq_state_independent (C := C) (F := F) f g ihf ihg
      (allocOnly_fallthrough hwf hinst f hf) s t

#print axioms allocOnly_fallthrough
#print axioms allocOnly_cost_independent
/-! ## The suffixes are allocator-only

`fakeMoves` produces only skip, instruction, move and seq nodes: the empty case is `.skip`, the step
is `.seq seqL (.move ...)` or `.seq seqL (fakeMove ...)` where `fakeMove v = .inst (.const v 0)`
(SSAFixInconsistencies.lean:36-57).  Hence every inconsistency-fixing suffix is `AllocOnly`. -/
/-- Auxiliary form: instead of projecting the tuple, the caller supplies the equation, so the
components are substituted definitionally by `cases`. -/
theorem fakeMoves_allocOnly_aux (prio : Option (Unit ⊕ Unit)) :
    ∀ (xs : List Nat) (ssaL ssaR : Spt Nat) (na : Nat)
      (l r : WordLangProgHOL (BitVec 64)) (na' : Nat) (sl sr : Spt Nat),
      Flapjack.Compiler.Backend.WordAlloc.fakeMoves (width := 64) prio xs ssaL ssaR na = (l, r, na', sl, sr) → AllocOnly l
  | [], ssaL, ssaR, na => by
      intro l r na' sl sr h
      simp only [Flapjack.Compiler.Backend.WordAlloc.fakeMoves] at h
      cases h
      exact AllocOnly.skip
  | x :: xs, ssaL, ssaR, na => by
      intro l r na' sl sr h
      obtain ⟨a, b, c, d, e, he⟩ :
          ∃ a b c d e, Flapjack.Compiler.Backend.WordAlloc.fakeMoves (width := 64) prio xs ssaL ssaR na = (a, b, c, d, e) :=
        ⟨_, _, _, _, _, rfl⟩
      have ih : AllocOnly a := fakeMoves_allocOnly_aux prio xs ssaL ssaR na a b c d e he
      have hfst : (a, b, c, d, e).1 = a := rfl
      simp only [Flapjack.Compiler.Backend.WordAlloc.fakeMoves] at h
      rw [he, hfst] at h
      split at h <;>
        (injection h with h1 _
         rw [← h1]
         first
           | exact ih
           | exact AllocOnly.seq a _ ih (AllocOnly.inst _)
           | exact AllocOnly.seq a _ ih (AllocOnly.move _ _))

/-- The projected form, for callers that only have the program. -/
theorem fakeMoves_allocOnly (prio : Option (Unit ⊕ Unit))
    (xs : List Nat) (ssaL ssaR : Spt Nat) (na : Nat) :
    AllocOnly (Flapjack.Compiler.Backend.WordAlloc.fakeMoves (width := 64) prio xs ssaL ssaR na).1 := by
  obtain ⟨p1, p2, p3, p4, p5, he⟩ :
      ∃ a b c d e, Flapjack.Compiler.Backend.WordAlloc.fakeMoves (width := 64) prio xs ssaL ssaR na = (a, b, c, d, e) :=
    ⟨_, _, _, _, _, rfl⟩
  have hb := he
  rw [he]
  show AllocOnly p1
  exact fakeMoves_allocOnly_aux prio xs ssaL ssaR na p1 p2 p3 p4 p5 hb

#print axioms fakeMoves_allocOnly_aux
#print axioms fakeMoves_allocOnly
/-- The inconsistency-fixing suffix itself is allocator-only: `fixInconsistencies` returns
`.seq (.move (priority prio true) lmov) lseq` (SSAFixInconsistencies.lean:71), whose second half is a
`fakeMoves` program. -/
theorem fixInconsistencies_allocOnly (prio : Option (Unit ⊕ Unit))
    (ssaL ssaR : Spt Nat) (na : Nat) :
    AllocOnly (Flapjack.Compiler.Backend.WordAlloc.fixInconsistencies (width := 64) prio ssaL ssaR na).1 := by
  unfold Flapjack.Compiler.Backend.WordAlloc.fixInconsistencies
  dsimp only [Prod.fst, Prod.snd]
  exact AllocOnly.seq _ _ (AllocOnly.move _ _) (fakeMoves_allocOnly prio _ _ _ _)

#print axioms fixInconsistencies_allocOnly
/-! ## Appending the allocator suffix to a compiled branch

The quantitative transfer of `first` against `bodyC` lifts to `first` against `bodyC` FOLLOWED BY the
inconsistency-fixing suffix, at the cost of one extra charge: the suffix's own cost, which is a
constant by state independence (`hsufCost`).  The suffix's fall-through (`hsufFall`) is what makes the
composite run keep the outcome - the suffix cannot escape, so the composite's result is the body's
result, which is already equal to the source's by the body's transfer.

This is the exact shape a compiled ite/loop/call branch has (`ssaCcTrans_ite_shape` wraps each branch
as `.seq body suffix`), so the constructor cases reduce to instantiating it. -/
theorem seq_suffix_transfer {C F : Type}
    (first bodyC suf : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (s0 : WordSemStateFiniteExact 64 C F)
    (hsufFall : ∀ (s : WordSemStateFiniteExact 64 C F), (fixClock s (WordSemStateFiniteExact.evaluate suf s)).1 = none)
    (hsufCost : ∀ (s t : WordSemStateFiniteExact 64 C F), wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice suf s = wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice suf t)
    (hbody : quantTransfer (C := C) (F := F) first bodyC source target extra) :
    quantTransfer (C := C) (F := F) first (.seq bodyC suf) source target
      (extra + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice suf s0) := by
  obtain ⟨⟨rS, sS, rT, sT, hrunS, hrunT, hout⟩, hcost⟩ := hbody
  have hpres : ∀ (res : Option (WordSemResult 64)) (mid : WordSemStateFiniteExact 64 C F),
      fixClock target (WordSemStateFiniteExact.evaluate bodyC target) = (res, mid) → res = rT := by
    intro res mid h
    have h1 := fixClock_fst target (WordSemStateFiniteExact.evaluate bodyC target)
    rw [h] at h1
    rw [hrunT] at h1
    simpa using h1
  cases hfx : fixClock target (WordSemStateFiniteExact.evaluate bodyC target) with
  | mk res mid =>
    have hres : res = rT := hpres res mid hfx
    cases res with
    | none =>
        have hrT : rT = none := hres.symm
        have hcomp : WordSemStateFiniteExact.evaluate (.seq bodyC suf) target = WordSemStateFiniteExact.evaluate suf mid :=
          evaluate_seq_none bodyC suf target mid hfx
        refine ⟨⟨none, sS, (WordSemStateFiniteExact.evaluate suf mid).1, (WordSemStateFiniteExact.evaluate suf mid).2, ?_, ?_, ?_⟩, ?_⟩
        · rw [hrunS, hout, hrT]
        · rw [hcomp]
        · rw [← fixClock_fst mid (WordSemStateFiniteExact.evaluate suf mid), hsufFall mid]
        · rw [wec_seq_none_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC suf target mid hfx,
              refinedWordLocalPrice_seq_zero bodyC suf target]
          have hs := hsufCost mid s0
          omega
    | some v =>
        have hnone : (fixClock target (WordSemStateFiniteExact.evaluate bodyC target)).1 = none → False := by
          intro h
          rw [hfx] at h
          cases h
        have hcomp : WordSemStateFiniteExact.evaluate (.seq bodyC suf) target = (some v, mid) :=
          evaluate_seq_escape bodyC suf target mid (some v) hfx (by intro h; cases h)
        refine ⟨⟨rS, sS, some v, mid, ?_, ?_, ?_⟩, ?_⟩
        · exact hrunS
        · exact hcomp
        · exact hout.trans hres.symm
        · rw [wec_seq_some_split_generic InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC suf target hnone,
              refinedWordLocalPrice_seq_zero bodyC suf target]
          omega

#print axioms seq_suffix_transfer
/-- A compiled branch: the body's transfer composes with the allocator suffix, whose two facts come
from the shape certificate rather than from hypotheses on the suffix's behaviour. -/
theorem compiled_branch_transfer {C F : Type}
    (first bodyC suf : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat) (s0 : WordSemStateFiniteExact 64 C F)
    (hwf : ∀ (pri : Nat) (moves : List (Nat × Nat)),
      (moves.map Prod.fst).Nodup ∧ ∀ (s : WordSemStateFiniteExact 64 C F), WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none)
    (hinst : ∀ (i : WordLangInst (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      (fixClock s (WordSemStateFiniteExact.evaluate (.inst i) s)).1 = none)
    (hsuf : AllocOnly suf)
    (hbody : quantTransfer (C := C) (F := F) first bodyC source target extra) :
    quantTransfer (C := C) (F := F) first (.seq bodyC suf) source target
      (extra + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice suf s0) :=
  seq_suffix_transfer first bodyC suf source target extra s0
    (allocOnly_fallthrough hwf hinst suf hsuf)
    (allocOnly_cost_independent hwf hinst suf hsuf) hbody

/-- The same, for the concrete suffix `fixInconsistencies` appends to a branch: its shape is
certified by fixInconsistencies_allocOnly, so no hypothesis about it remains. -/
theorem fixInconsistencies_suffix_transfer {C F : Type}
    (first bodyC : WordLangProgHOL (BitVec 64))
    (prio : Option (Unit ⊕ Unit)) (ssaL ssaR : Spt Nat) (na : Nat)
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat) (s0 : WordSemStateFiniteExact 64 C F)
    (hwf : ∀ (pri : Nat) (moves : List (Nat × Nat)),
      (moves.map Prod.fst).Nodup ∧ ∀ (s : WordSemStateFiniteExact 64 C F), WordSemStateFiniteExact.getVars (moves.map Prod.snd) s ≠ none)
    (hinst : ∀ (i : WordLangInst (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      (fixClock s (WordSemStateFiniteExact.evaluate (.inst i) s)).1 = none)
    (hbody : quantTransfer (C := C) (F := F) first bodyC source target extra) :
    quantTransfer (C := C) (F := F) first
      (.seq bodyC (Flapjack.Compiler.Backend.WordAlloc.fixInconsistencies (width := 64) prio ssaL ssaR na).1)
      source target
      (extra + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (Flapjack.Compiler.Backend.WordAlloc.fixInconsistencies (width := 64) prio ssaL ssaR na).1 s0) :=
  compiled_branch_transfer first bodyC _ source target extra s0 hwf hinst
    (fixInconsistencies_allocOnly prio ssaL ssaR na) hbody

#print axioms compiled_branch_transfer
#print axioms fixInconsistencies_suffix_transfer
/-! ## The quantitative ite constructor

Both halves come from facts already proved: the simulation half is the compiler's own ite correctness
(ssaCcTransCorrectIf, with its invariant IHs), and the quantitative half is the program-parametric
transfer of the compiled ite, which ite_quantTransfer_then builds from the SELECTED branch's transfer
and the comparison that selects it.  The only extra input is the compiled program's shape, i.e. that
the compiler's ite really is that .ite node - exactly what ssaCcTrans_ite_shape states. -/
theorem ssaCcTrans_ite_quant_then {C F : Type}
    (cmp : Cmp) (left : Nat) (immediate : WordRegImm (BitVec 64))
    (left' : Nat) (immediate' : WordRegImm (BitVec 64))
    (first second thenB elseB : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (extra : Nat)
    (firstIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat)
      (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) first = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation first source target ssa next tables)
    (secondIH : ∀ (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat)
      (tables : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) second = true ∧
      ssaMapOK next ssa ∧ ltOK tables → ssaSimulation second source target ssa next tables)
    (hinv : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.ite cmp left immediate first second) = true ∧
      ssaMapOK next ssa ∧ ltOK tables)
    (hshape : (ssaCcTrans (.ite cmp left immediate first second) ssa next tables).1 =
      .ite cmp left' immediate' thenB elseB)
    (xS yS xT yT : WordLocW 64)
    (hxS : getVar left source = some xS) (hyS : getVarImm immediate source = some yS)
    (hcS : wordSemWordCmp cmp xS yS = some true)
    (hxT : getVar left' target = some xT) (hyT : getVarImm immediate' target = some yT)
    (hcT : wordSemWordCmp cmp xT yT = some true)
    (hbr : quantTransfer (C := C) (F := F) first thenB source target extra) :
    quantSsaSimulation (.ite cmp left immediate first second) source target ssa next tables extra := by
  obtain ⟨⟨rS, sS, rT, sT, hrunS, hrunT, hout⟩, hcost⟩ :=
    ite_quantTransfer_then cmp left left' immediate immediate' first second thenB elseB
      source target extra xS yS xT yT hxS hyS hcS hxT hyT hcT hbr
  refine ⟨Flapjack.Compiler.Backend.WordAlloc.ssaCcTransCorrectIf cmp left immediate first second source target ssa next tables
    firstIH secondIH hinv, ⟨rS, sS, rT, sT, hrunS, ?_, hout⟩, ?_⟩
  · rw [hshape]
    exact hrunT
  · rw [hshape]
    exact hcost

#print axioms ssaCcTrans_ite_quant_then
/-- A loop node whose cut state is absent charges only its node price (2). -/
theorem wec_loop_cutState_none {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = none) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s = 2 := by
  rw [wordExecutionCost]
  split
  · rw [refinedWordLocalPrice_loop]
  · next hsome =>
    rw [hs] at hsome
    cases hsome

#print axioms wec_loop_cutState_none
/-- The loop node's cost decomposition over its body run: node price plus the body's cost plus, when
the body's result continues the loop, the next iteration's cost (at the decremented clock, and zero
when the clock is exhausted).  Stated with the same `let` and `if`/`dite` binding structure as the
counter's clause, so the proof is the clause's own case analysis. -/
theorem wec_loop_split {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s cutSource : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cutSource)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (h : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) = (result, middle)) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s +
        wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutSource +
        (if wordSemContLoop result then
          (dite (middle.clock = 0) (fun _ => 0)
            (fun _ => wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (wordSemSTOP (.loop names body liveOut))
              (Flapjack.WordSemStateFiniteExact.decClock middle)))
         else 0) := by
  rw [wordExecutionCost]
  split
  · next hnone =>
    rw [hs] at hnone
    cases hnone
  · next cs hsome =>
    rw [hs] at hsome
    cases hsome
    cases hfix : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) with
    | mk r m =>
      rw [hfix] at h
      cases h
      rfl

#print axioms wec_loop_split
/-- When the body's result does not continue the loop, the loop charges only its node price and the
body's work. -/
theorem wec_loop_stop {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s cutSource : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cutSource)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (h : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) = (result, middle))
    (hnc : wordSemContLoop result = false) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutSource := by
  rw [wec_loop_split names liveOut body s cutSource hs result middle h, hnc]
  simp

/-- When it does, the next iteration is charged at the decremented clock (zero once exhausted). -/
theorem wec_loop_cont {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s cutSource : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cutSource)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (h : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) = (result, middle))
    (hc : wordSemContLoop result = true) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s =
      InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutSource +
        (dite (middle.clock = 0) (fun _ => 0)
          (fun _ => wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (wordSemSTOP (.loop names body liveOut))
            (Flapjack.WordSemStateFiniteExact.decClock middle))) := by
  rw [wec_loop_split names liveOut body s cutSource hs result middle h, hc]
  simp

#print axioms wec_loop_stop
#print axioms wec_loop_cont
/-- The call node's third flat-price path: the frame lookup fails.  Note the hypothesis is about the
argument list itself: wordSemAddRetLoc none xs = xs by definition, so the counter's lookup is the lookup
at xs, and no statement has to name wordSemAddRetLoc's implicit return-type parameters. -/
theorem wec_call_none_findCode_none {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hgv : WordSemStateFiniteExact.getVars args s = some xs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfc : wordSemFindCode dest xs s.code s.stackSize = none) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args handler) s = 41 := by
  simp [wordExecutionCost, hgv, hbad, wordSemAddRetLoc, hfc, refinedWordLocalPrice_call_none]

#print axioms wec_call_none_findCode_none
/-! ## The global relation between original and transformed code

The local constructors say what a transformed BODY is worth.  What a call charges, however, is a body
FETCHED from the code by wordSemFindCode - so the missing global ingredient is a relation between the
original code and the transformed code, saying that each callee the program can reach has been replaced
by a body that is a quantitative transfer of it.  Stated with quantTransfer, the relation carries
exactly the data a call site needs: the two runs agree on their outcome, and the transformed body
charges no more than the original plus the per-function budget. -/
def transformedCalleeRel {C F : Type}
    (origCode transCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (budget : Nat) : Prop :=
  ∀ (dest arity : Nat) (body bodyC : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F),
    sptLookup dest origCode = some (arity, body) →
    sptLookup dest transCode = some (arity, bodyC) →
    quantTransfer (C := C) (F := F) body bodyC source target budget

/-- What a call site needs from the global relation, at the frame it actually fetched: the two runs
agree on their outcome, and the transformed callee is at most the original plus the budget. -/
theorem transformedCalleeRel.spec {C F : Type}
    (origCode transCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (budget : Nat)
    (hrel : transformedCalleeRel (C := C) (F := F) origCode transCode budget)
    (dest arity : Nat) (body bodyC : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (h1 : sptLookup dest origCode = some (arity, body))
    (h2 : sptLookup dest transCode = some (arity, bodyC)) :
    (∃ rS : Option (WordSemResult 64), ∃ sS : WordSemStateFiniteExact 64 C F,
      ∃ rT : Option (WordSemResult 64), ∃ sT : WordSemStateFiniteExact 64 C F,
      WordSemStateFiniteExact.evaluate body source = (rS, sS) ∧
      WordSemStateFiniteExact.evaluate bodyC target = (rT, sT) ∧ rS = rT) ∧
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC target ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body source + budget :=
  hrel dest arity body bodyC source target h1 h2

#print axioms transformedCalleeRel.spec
/-- The frame that wordSemFindCode returns comes from a lookup in the code table: this is the seam
between the call's accounting (which unpacks the returned code and stack size) and the global
transformedCalleeRel (which is stated over sptLookup). -/
theorem findCode_some_lookup {StackSize : Type}
    (dest : Nat) (ys : List (WordLocW 64))
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (ss : Spt StackSize)
    (args' : List (WordLocW 64)) (body : WordLangProgHOL (BitVec 64)) (ssOpt : Option StackSize)
    (h : wordSemFindCode (some dest) ys code ss = some (args', body, ssOpt)) :
    ∃ arity, sptLookup dest code = some (arity, body) ∧ args' = ys ∧ ssOpt = sptLookup dest ss := by
  cases hlk : sptLookup dest code with
  | none =>
    simp only [wordSemFindCode, hlk] at h
    cases h
  | some pair =>
    obtain ⟨arity, exp⟩ := pair
    simp only [wordSemFindCode, hlk] at h
    split at h
    · cases h
      exact ⟨arity, rfl, rfl, rfl⟩
    · cases h

#print axioms findCode_some_lookup
/-! ## The quantitative transfer at the optimizer price

`WordOptimizerPrice.lean` prices a move node at 24 per pair and floors the instruction/get/loc/heap heads
at 24; everything else is the refined price.  Downstream passes (CSE, copy propagation) are proved
against THAT price, so the SSA/allocator transfer has to be available there too.

The port rides a seam that costs nothing to exploit: the RUN half of a transfer never mentions a price.
So `quantTransferAt` takes the price as a parameter, its run component is literally the one already
proved at the refined price, and its cost component is re-derived with the counter splits, which are
already price-polymorphic. -/

/-- The run half of a transfer: the two programs have outcome-equal runs.  Price-free. -/
noncomputable def quantRuns {C F : Type}
    (prog compiledProg : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ rS : Option (WordSemResult 64), ∃ sS : WordSemStateFiniteExact 64 C F,
  ∃ rT : Option (WordSemResult 64), ∃ sT : WordSemStateFiniteExact 64 C F,
    WordSemStateFiniteExact.evaluate prog source = (rS, sS) ∧
    WordSemStateFiniteExact.evaluate compiledProg target = (rT, sT) ∧
    rS = rT

/-- The quantitative transfer at an arbitrary price: price-free runs plus a counter bound. -/
noncomputable def quantTransferAt {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (prog compiledProg : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat) : Prop :=
  quantRuns prog compiledProg source target ∧
  wordExecutionCost price compiledProg target ≤ wordExecutionCost price prog source + extra

theorem quantRuns.of_quantTransfer {C F : Type}
    (prog compiledProg : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (h : quantTransfer (C := C) (F := F) prog compiledProg source target extra) :
    quantRuns prog compiledProg source target :=
  h.1

theorem quantTransferAt.summary {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (prog compiledProg : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (h : quantTransferAt price prog compiledProg source target extra) :
    quantRuns prog compiledProg source target ∧
    wordExecutionCost price compiledProg target ≤
      wordExecutionCost price prog source + extra :=
  h

/-! ### The optimizer price at each head -/

theorem wordOptimizerLocalPrice_move {C F : Type} (pri : Nat) (pairs : List (Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.move pri pairs) s = 24 * pairs.length := rfl

theorem wordOptimizerLocalPrice_seq_zero {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.seq f g) s = 0 := by
  simp only [wordOptimizerLocalPrice, refinedWordLocalPrice_seq_zero]

theorem wordOptimizerLocalPrice_ite {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64))
    (e2 e3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.ite cmp r1 ri e2 e3) s = 23 := by
  simp only [wordOptimizerLocalPrice, refinedWordLocalPrice_ite]

theorem wordOptimizerLocalPrice_loop {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.loop names body liveOut) s = 2 := by
  simp only [wordOptimizerLocalPrice, refinedWordLocalPrice_loop]

theorem wordOptimizerLocalPrice_call_none {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.call none dest args handler) s = 41 := by
  simp only [wordOptimizerLocalPrice, refinedWordLocalPrice_call_none]

/-! ### The counter at the optimizer price -/

/-- A move node charges exactly its node price, at the optimizer price too. -/
theorem wec_move_optimizer {C F : Type} (pri : Nat) (moves : List (Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.move pri moves) s = 24 * moves.length := by
  rw [wec_move_generic wordOptimizerLocalPrice, wordOptimizerLocalPrice_move]

theorem wec_seq_none_split_optimizer {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s mid : WordSemStateFiniteExact 64 C F)
    (h : fixClock s (WordSemStateFiniteExact.evaluate f s) = (none, mid)) :
    wordExecutionCost wordOptimizerLocalPrice (.seq f g) s =
      wordExecutionCost wordOptimizerLocalPrice f s + wordExecutionCost wordOptimizerLocalPrice g mid := by
  rw [wec_seq_none_split_generic wordOptimizerLocalPrice f g s mid h, wordOptimizerLocalPrice_seq_zero]
  omega

theorem wec_seq_some_split_optimizer {C F : Type}
    (f g : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (h : (fixClock s (WordSemStateFiniteExact.evaluate f s)).1 = none → False) :
    wordExecutionCost wordOptimizerLocalPrice (.seq f g) s =
      wordExecutionCost wordOptimizerLocalPrice f s := by
  rw [wec_seq_some_split_generic wordOptimizerLocalPrice f g s h, wordOptimizerLocalPrice_seq_zero]
  omega

/-! ### The transformed-callee relation at the optimizer price -/

def transformedCalleeRelAt {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (origCode transCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (budget : Nat) : Prop :=
  ∀ (dest arity : Nat) (body bodyC : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F),
    sptLookup dest origCode = some (arity, body) →
    sptLookup dest transCode = some (arity, bodyC) →
    quantTransferAt price body bodyC source target budget

theorem transformedCalleeRelAt.spec {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (origCode transCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (budget : Nat)
    (hrel : transformedCalleeRelAt (C := C) (F := F) price origCode transCode budget)
    (dest arity : Nat) (body bodyC : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (h1 : sptLookup dest origCode = some (arity, body))
    (h2 : sptLookup dest transCode = some (arity, bodyC)) :
    quantRuns body bodyC source target ∧
    wordExecutionCost price bodyC target ≤
      wordExecutionCost price body source + budget :=
  quantTransferAt.summary price body bodyC source target budget
    (hrel dest arity body bodyC source target h1 h2)

#print axioms quantTransferAt.summary
#print axioms wec_move_optimizer
#print axioms wec_seq_none_split_optimizer
#print axioms transformedCalleeRelAt.spec
/-! ### The optimizer price against the certified coalescing table

The optimizer price charges 24 per move PAIR, while the certified table charges 12 per emitted move and
its budget is 24 per NON-self pair.  Those two are not comparable per pair: a swap of two locals emits
two moves, so at 24 per pair the optimizer price can be twice the table's charge for the same node.
The honest certificate is therefore the doubled one (and it is what composes: a factor two on the
inserted-move charge, which is what the upstream optimizer's own price is documented to pay). -/

/-- At the optimizer price an inserted move node is paid by twice the certified table charge. -/
theorem optimizer_move_price_le_double_table {C F : Type} (pri : Nat)
    (pairs : List (Nat × Nat)) (before : Nat) (s : WordSemStateFiniteExact 64 C F)
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    24 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length ≤
      2 * allocMovePrice pairs := by
  have h := goSeq_move ok
  omega

/-- The same bound in the form the scheduler states its budget. -/
theorem optimizer_move_price_le_nonself {C F : Type} (pri : Nat)
    (pairs : List (Nat × Nat)) (before : Nat) (s : WordSemStateFiniteExact 64 C F)
    (ok : (goSeq before (.move pri pairs)).1 = true) :
    24 * (Flapjack.Compiler.Backend.Parmove.parmove (physPairs pairs)).length ≤
      56 * nonselfCount pairs := by
  have h := goSeq_move ok
  have h2 := allocMovePrice_le pairs
  omega

#print axioms optimizer_move_price_le_double_table
#print axioms optimizer_move_price_le_nonself
/-! ### The allocator-only leaves are state independent at the optimizer price

These are the per-constructor facts that `allocOnly_cost_independent` consumes.  At the optimizer price the
move head charges 24 per pair (no state), the instruction head charges max 24 (refined price) (no state),
and every other allocator-only head is the refined price, which is state independent.  So the same
suffix certificate is available at the optimizer price - the run half (move_fallthrough, seq_fallthrough)
is about `evaluate` and therefore already price free. -/

theorem wordOptimizerLocalPrice_inst {C F : Type} (i : WordLangInst (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (.inst i) s = max 24 (InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.inst i) s) := rfl

theorem wec_skip_optimizer_state_independent {C F : Type}
    (s t : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (WordLangProgHOL.skip) s =
      wordExecutionCost wordOptimizerLocalPrice (WordLangProgHOL.skip) t := by
  rw [wec_skip wordOptimizerLocalPrice, wec_skip wordOptimizerLocalPrice]
  simp only [wordOptimizerLocalPrice]
  exact refinedWordLocalPrice_state_independent _ s t

theorem wec_inst_optimizer_state_independent {C F : Type}
    (i : WordLangInst (BitVec 64)) (s t : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.inst i) s = wordExecutionCost wordOptimizerLocalPrice (.inst i) t := by
  rw [wec_inst wordOptimizerLocalPrice, wec_inst wordOptimizerLocalPrice]
  simp only [wordOptimizerLocalPrice]
  rw [refinedWordLocalPrice_state_independent (WordLangProgHOL.inst i) s t]

theorem wec_move_optimizer_state_independent {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s t : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.move pri moves) s =
      wordExecutionCost wordOptimizerLocalPrice (.move pri moves) t := by
  rw [wec_move_optimizer, wec_move_optimizer]

#print axioms wec_skip_optimizer_state_independent
#print axioms wec_inst_optimizer_state_independent
#print axioms wec_move_optimizer_state_independent
/-- The call node's successful path, in the form the callee's transfer consumes: with the frame looked
up, a live clock and no handler, the call charges its node price plus the CALLEE's cost at the environment
the call constructs (callEnv at the returned arguments, the looked-up stack size, and the decremented
clock).  That environment is exactly the state transformedCalleeRel.spec delivers a bound for, and the
frame is exactly what findCode_some_lookup turns into the code-table lookups .spec asks for. -/
theorem wec_call_none_success {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hgv : WordSemStateFiniteExact.getVars args s = some xs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfc : wordSemFindCode dest xs s.code s.stackSize = some (args1, prog, ss))
    (hclk : s.clock = 0 → False) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args none) s =
      41 + wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice prog
        (Flapjack.WordSemStateFiniteExact.callEnv args1 ss (Flapjack.WordSemStateFiniteExact.decClock s)) := by
  rw [wordExecutionCost, hgv]
  dsimp only
  rw [if_neg (by rw [hbad]; decide : ¬ (wordSemBadDestArgs dest args = true))]
  simp only [wordSemAddRetLoc]
  rw [hfc]
  dsimp only
  rw [dif_neg hclk]
  simp only [refinedWordLocalPrice_call_none]

#print axioms wec_call_none_success
/-- The call node's transfer, in its final form: if the two programs' call sites look up their frames
(the original's callee and the transformed one's) and the transformed callee charges at most the
original's plus a budget AT THE ENVIRONMENTS THE CALLS CONSTRUCT, then the whole call node transfers
within the same budget.  The callee hypothesis is exactly what transformedCalleeRel.spec supplies, and
the two frames are exactly what findCode_some_lookup supplies. -/
theorem wec_call_none_callee_transfer {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (s s' : WordSemStateFiniteExact 64 C F) (xs xs' : List (WordLocW 64))
    (args1 args1' : List (WordLocW 64)) (prog progC : WordLangProgHOL (BitVec 64))
    (ss ss' : Option Nat) (budget : Nat)
    (hgv : WordSemStateFiniteExact.getVars args s = some xs)
    (hgv' : WordSemStateFiniteExact.getVars args s' = some xs')
    (hbad : wordSemBadDestArgs dest args = false)
    (hbad' : wordSemBadDestArgs dest args = false)
    (hfc : wordSemFindCode dest xs s.code s.stackSize = some (args1, prog, ss))
    (hfc' : wordSemFindCode dest xs' s'.code s'.stackSize = some (args1', progC, ss'))
    (hclk : s.clock = 0 → False) (hclk' : s'.clock = 0 → False)
    (hcallee :
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice progC (Flapjack.WordSemStateFiniteExact.callEnv args1' ss'
          (Flapjack.WordSemStateFiniteExact.decClock s')) ≤
        wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice prog (Flapjack.WordSemStateFiniteExact.callEnv args1 ss
          (Flapjack.WordSemStateFiniteExact.decClock s)) + budget) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args none) s' ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.call none dest args none) s + budget := by
  rw [wec_call_none_success dest args s xs args1 prog ss hgv hbad hfc hclk,
    wec_call_none_success dest args s' xs' args1' progC ss' hgv' hbad' hfc' hclk']
  omega

#print axioms wec_call_none_callee_transfer
/-- The loop node's transfer when the body's result continues the loop and BOTH clocks are exhausted:
neither side charges a further iteration, so again only the node prices and the bodies remain. -/
theorem wec_loop_cont_done_transfer {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body bodyC : WordLangProgHOL (BitVec 64))
    (s t cutS cutT : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (hs : cutState (names, .ln) s = some cutS)
    (ht : cutState (names, .ln) t = some cutT)
    (resultS : Option (WordSemResult 64)) (midS : WordSemStateFiniteExact 64 C F)
    (resultT : Option (WordSemResult 64)) (midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock cutS (WordSemStateFiniteExact.evaluate body cutS) = (resultS, midS))
    (hT : fixClock cutT (WordSemStateFiniteExact.evaluate bodyC cutT) = (resultT, midT))
    (hcS : wordSemContLoop resultS = true)
    (hcT : wordSemContLoop resultT = true)
    (hcost : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC cutT ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutS + extra)
    (hzS : midS.clock = 0) (hzT : midT.clock = 0) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names bodyC liveOut) t ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s + extra := by
  rw [wec_loop_cont names liveOut bodyC t cutT ht resultT midT hT hcT,
    wec_loop_cont names liveOut body s cutS hs resultS midS hS hcS]
  rw [dif_pos hzT, dif_pos hzS]
  simp only [refinedWordLocalPrice_loop]
  omega

/-- The loop node's transfer when the body's result continues the loop and BOTH clocks are live: each side
charges one further iteration, so the node transfers whenever the body and the next iteration do.  The
budget is doubled because BOTH the body and the recursive iteration are charged, one extra each - this is
the step case of the loop's clock induction, with the recursive call explicit. -/
theorem wec_loop_cont_live_transfer {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body bodyC : WordLangProgHOL (BitVec 64))
    (s t cutS cutT : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (hs : cutState (names, .ln) s = some cutS)
    (ht : cutState (names, .ln) t = some cutT)
    (resultS : Option (WordSemResult 64)) (midS : WordSemStateFiniteExact 64 C F)
    (resultT : Option (WordSemResult 64)) (midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock cutS (WordSemStateFiniteExact.evaluate body cutS) = (resultS, midS))
    (hT : fixClock cutT (WordSemStateFiniteExact.evaluate bodyC cutT) = (resultT, midT))
    (hcS : wordSemContLoop resultS = true)
    (hcT : wordSemContLoop resultT = true)
    (hcost : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC cutT ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutS + extra)
    (hclkS : midS.clock = 0 → False) (hclkT : midT.clock = 0 → False)
    (hrec :
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (wordSemSTOP (.loop names bodyC liveOut)) (Flapjack.WordSemStateFiniteExact.decClock midT) ≤
        wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (wordSemSTOP (.loop names body liveOut)) (Flapjack.WordSemStateFiniteExact.decClock midS) + extra) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names bodyC liveOut) t ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s + (extra + extra) := by
  rw [wec_loop_cont names liveOut bodyC t cutT ht resultT midT hT hcT,
    wec_loop_cont names liveOut body s cutS hs resultS midS hS hcS]
  rw [dif_neg hclkT, dif_neg hclkS]
  simp only [refinedWordLocalPrice_loop]
  omega

#print axioms wec_loop_cont_done_transfer
#print axioms wec_loop_cont_live_transfer
/-- The loop node's transfer in the case where the body's result does NOT continue the loop: the loop
charges its node price plus the body's work on both sides, so the two node prices cancel and the whole
node transfers whenever the body does.  This is the base case of the loop's clock induction; the
continuing case recurses through wec_loop_cont. -/
theorem wec_loop_stop_transfer {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body bodyC : WordLangProgHOL (BitVec 64))
    (s t cutS cutT : WordSemStateFiniteExact 64 C F) (extra : Nat)
    (hs : cutState (names, .ln) s = some cutS)
    (ht : cutState (names, .ln) t = some cutT)
    (resultS : Option (WordSemResult 64)) (midS : WordSemStateFiniteExact 64 C F)
    (resultT : Option (WordSemResult 64)) (midT : WordSemStateFiniteExact 64 C F)
    (hS : fixClock cutS (WordSemStateFiniteExact.evaluate body cutS) = (resultS, midS))
    (hT : fixClock cutT (WordSemStateFiniteExact.evaluate bodyC cutT) = (resultT, midT))
    (hncS : wordSemContLoop resultS = false)
    (hncT : wordSemContLoop resultT = false)
    (hcost : wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice bodyC cutT ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice body cutS + extra) :
    wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names bodyC liveOut) t ≤
      wordExecutionCost InitECandidate.Runtime.WordToStack.refinedWordLocalPrice (.loop names body liveOut) s + extra := by
  rw [wec_loop_stop names liveOut bodyC t cutT ht resultT midT hT hncT,
    wec_loop_stop names liveOut body s cutS hs resultS midS hS hncS]
  simp only [refinedWordLocalPrice_loop]
  omega

#print axioms wec_loop_stop_transfer
/-! ### The loop's run, mirroring its cost decomposition

The evaluator's loop clause (Evaluate.lean:192-207): cut the state, run the body, and then - if the body's
result continues the loop - either time out at a zero clock or recurse at wordSemSTOP of the loop and the
decremented clock; otherwise, for a `break 0`, consult the exit names, and for anything else return
wordSemExitLoop of the result.  These are the run shapes the loop's induction steps on, matching
wec_loop_stop and wec_loop_cont on the cost side. -/
theorem evaluate_loop_stop {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s cutSource : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cutSource)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (h : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) = (result, middle))
    (hnc : wordSemContLoop result = false)
    (hbreak : result = some (.break 0) → False) :
    WordSemStateFiniteExact.evaluate (.loop names body liveOut) s = (wordSemExitLoop result, middle) := by
  rw [evaluate]
  split
  · next hnone =>
    rw [hs] at hnone
    cases hnone
  · next cs hsome =>
    rw [hs] at hsome
    cases hsome
    rw [h]
    dsimp only
    rw [if_neg (by rw [hnc]; decide : ¬ (wordSemContLoop result = true))]
    split
    · exact absurd rfl hbreak
    · rfl


#print axioms evaluate_loop_stop
/-- The loop's CONTINUING run: when the body's result continues the loop and the body did not exhaust the
clock, the loop evaluates exactly to a further iteration - wordSemSTOP of the loop at the decremented
clock.  This is the run-level counterpart of wec_loop_cont_live_transfer, and it is the step the loop's
outcome induction takes. -/
theorem evaluate_loop_cont {C F : Type}
    (names liveOut : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (s cutSource : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cutSource)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (h : fixClock cutSource (WordSemStateFiniteExact.evaluate body cutSource) = (result, middle))
    (hc : wordSemContLoop result = true)
    (hclk : middle.clock = 0 → False) :
    WordSemStateFiniteExact.evaluate (.loop names body liveOut) s =
      WordSemStateFiniteExact.evaluate (wordSemSTOP (.loop names body liveOut)) (Flapjack.WordSemStateFiniteExact.decClock middle) := by
  rw [evaluate]
  split
  · next hnone =>
    rw [hs] at hnone
    cases hnone
  · next cs hsome =>
    rw [hs] at hsome
    cases hsome
    rw [h]
    dsimp only
    rw [if_pos (by rw [hc])]
    split
    · next hz =>
      exact absurd hz hclk
    · rfl

#print axioms evaluate_loop_cont
end InitECandidate.Runtime.FineCost
