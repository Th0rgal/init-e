import InitECandidate.Runtime.AllocCostSSAStackSwapWork

/-!
# `nativeWordPrice`: syntax-kind pricing for the post-allocation Word program

The fine executed-work counter `wordExecutionCost price` is parametric in a
`price : WordLangProgHOL (BitVec 64) → state → Nat`.  This module supplies the
*native* price: the price of one node is determined by its syntax kind alone,
never by a whole-program maximum, a code-table size or a uniform word budget.

Instruction categories mirror the committed native instruction table
(`skip 7`, `const 19`, `binopImm 21`, `binopReg 28`, `shiftImm 25`,
`shiftReg 32`, `div 28`, `longMul 22`, `longDiv 29`, other arithmetic `43`,
every memory access `21`; all values `≤ 43`).  Register identifiers do not
occur in the price, so the price is invariant under register renaming, whether
alpha-renaming or a physical allocation.

Parallel moves are priced by their *actual* size: a singleton move costs `14`,
a general move costs `28` per moved word.  Calls are priced by their actual
argument list and, for a returning call, by their actual return arity — but
only when the callee body actually returns a value list of that arity, which is
the state-dependent `wordCallReturned` used by the Loop-to-Word price as well.
A tail call pays the fixed `41` jump overhead; its argument copy is the priced
`Move` inserted by the allocator, so it is not charged twice.

Control nodes and leaves that native lowering removes or fuses (structure,
`tick`, `Get`/`Set`/`Store` after allocation) are free here: the instructions
they were lowered to are priced, not the source shape.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open Classical
open InitECandidate.Runtime.WordToStack

/-- Native category price of one post-allocation instruction.  Register
identifiers are ignored, so the price is renaming invariant. -/
def nativeInstPrice : WordLangInst (BitVec 64) → Nat
  | .skip => 7
  | .const _ _ => 19
  | .arith (.binop _ _ _ (.imm _)) => 21
  | .arith (.binop _ _ _ (.reg _)) => 28
  | .arith (.shift _ _ _ (.imm _)) => 25
  | .arith (.shift _ _ _ (.reg _)) => 32
  | .arith (.div _ _ _) => 28
  | .arith (.longMul _ _ _ _) => 22
  | .arith (.longDiv _ _ _ _ _) => 29
  | .arith (.addCarry _ _ _ _) => 43
  | .arith (.addOverflow _ _ _ _) => 43
  | .arith (.subOverflow _ _ _ _) => 43
  | .mem _ _ _ => 21

/-- Every instruction category is capped by `43`. -/
theorem nativeInstPrice_le (instruction : WordLangInst (BitVec 64)) :
    nativeInstPrice instruction ≤ 43 := by
  cases instruction with
  | skip => simp [nativeInstPrice]
  | const d v => simp [nativeInstPrice]
  | mem op d a => simp [nativeInstPrice]
  | arith operation =>
      cases operation with
      | binop operator destination source right =>
          cases right <;> simp [nativeInstPrice]
      | shift operator destination source right =>
          cases right <;> simp [nativeInstPrice]
      | div d1 d2 d3 => simp [nativeInstPrice]
      | longMul a b c d => simp [nativeInstPrice]
      | longDiv a b c d e => simp [nativeInstPrice]
      | addCarry a b c d => simp [nativeInstPrice]
      | addOverflow a b c d => simp [nativeInstPrice]
      | subOverflow a b c d => simp [nativeInstPrice]

/-- The native (post-allocation) price of one Word node.  Structural nodes are
free; instructions pay their category cap; parallel moves pay their actual
size; calls pay their actual arguments and, conditionally on the callee
actually returning that arity, their actual return count. -/
noncomputable def nativeWordPrice {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Nat :=
  match p with
  | .skip => 0
  | .move _ moves => (if moves.length ≤ 1 then 14 else 28) * moves.length
  | .inst instruction => nativeInstPrice instruction
  | .call none _ arguments _ => 41
  | .call (some (returns, _)) _ arguments _ =>
      189 + 39 * (arguments.length + 1 - 22) +
        if wordCallReturned p s then 21 * returns.length else 0
  | _ => 0

/-- A singleton parallel move pays `14`; a general one pays `28` per word. -/
theorem nativeWordPrice_move {C F : Type} (priority : Nat) (moves : List (Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.move priority moves) s =
      (if moves.length ≤ 1 then 14 else 28) * moves.length := by
  rw [nativeWordPrice]

/-- A returning call whose callee actually returns pays its return suffix; the
price depends on the run, not on a static maximum. -/
theorem nativeWordPrice_call_returning {C F : Type} (returns : List Nat)
    (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    nativeWordPrice (.call (some (returns, cutset, retCode, l1, l2)) dest arguments handler) s =
      189 + 39 * (arguments.length + 1 - 22) +
        if wordCallReturned (.call (some (returns, cutset, retCode, l1, l2)) dest arguments
          handler) s then 21 * returns.length else 0 := by
  rw [nativeWordPrice]

/-- The native price is invariant under replacing the stack by a value-equal
one: no instruction category, move size or argument/return list reads it. -/
theorem nativeWordPrice_stack {C F : Type} (q : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (ys : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq t.stack ys) :
    nativeWordPrice q { t with stack := ys } = nativeWordPrice q t := by
  cases q with
  | call ret dest args handler =>
      cases ret with
      | none => simp only [nativeWordPrice]
      | some triple =>
          obtain ⟨rets, cutset, retCode, l1, l2⟩ := triple
          rw [nativeWordPrice, nativeWordPrice,
            wordCallReturned_stack
              (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t ys hval]
  | skip => simp only [nativeWordPrice]
  | move priority moves => simp only [nativeWordPrice]
  | inst instruction => simp only [nativeWordPrice]
  | assign name value => simp only [nativeWordPrice]
  | get destination store => simp only [nativeWordPrice]
  | set store value => simp only [nativeWordPrice]
  | store address value => simp only [nativeWordPrice]
  | mustTerminate body => simp only [nativeWordPrice]
  | seq first second => simp only [nativeWordPrice]
  | ite operator condition right thenBranch elseBranch =>
      simp only [nativeWordPrice]
  | loop liveIn body liveOut => simp only [nativeWordPrice]
  | alloc destination cutsets => simp only [nativeWordPrice]
  | storeConsts source bitmap codeLength dataLength constants =>
      simp only [nativeWordPrice]
  | raise exception => simp only [nativeWordPrice]
  | «return» label values => simp only [nativeWordPrice]
  | «break» label => simp only [nativeWordPrice]
  | «continue» label => simp only [nativeWordPrice]
  | tick => simp only [nativeWordPrice]
  | opCurrHeap operator destination source => simp only [nativeWordPrice]
  | locValue destination source => simp only [nativeWordPrice]
  | install codeBuffer codeLength dataBuffer dataLength cutsets =>
      simp only [nativeWordPrice]
  | codeBufferWrite address value => simp only [nativeWordPrice]
  | dataBufferWrite address value => simp only [nativeWordPrice]
  | ffi function configuration configurationLength array arrayLength live =>
      simp only [nativeWordPrice]
  | shareInst operator name address => simp only [nativeWordPrice]

/-- **Native executed-cost invariance under a value-equal stack swap.** -/
theorem wordExecutionCost_nativeWordPrice_stack_variant {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (xs : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq s.stack xs)
    (hne : (evaluate p s).1 ≠ some WordSemResult.error) :
    InitECandidate.Runtime.FineCost.wordExecutionCost
        InitECandidate.Runtime.FineCost.nativeWordPrice p { s with stack := xs } =
      InitECandidate.Runtime.FineCost.wordExecutionCost
        InitECandidate.Runtime.FineCost.nativeWordPrice p s :=
  wec_stack_variant_dispatch InitECandidate.Runtime.FineCost.nativeWordPrice
    nativeWordPrice_stack p s xs hval hne

#print axioms nativeInstPrice_le
#print axioms nativeWordPrice_move
#print axioms nativeWordPrice_call_returning
#print axioms nativeWordPrice_stack
#print axioms wordExecutionCost_nativeWordPrice_stack_variant

end InitECandidate.Runtime.FineCost
