import InitECandidate.Runtime.AllocCostSSAStageCases
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans

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

#print axioms ssaCcTrans_seq_shape
#print axioms merge_overhead_bound
#print axioms ssaCcTrans_inst_shape
#print axioms ssaCcTrans_assign_shape
#print axioms ssaCcTrans_assign_cost
#print axioms nativeWordPrice_move_length
#print axioms ssaCcTrans_move_cost
#print axioms ssaCcTrans_inst_cost

end InitECandidate.Runtime.FineCost
