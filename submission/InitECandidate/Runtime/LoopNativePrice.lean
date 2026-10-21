import InitECandidate.Runtime.SourceCostLoopWorkP
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Native-calibrated Loop prices, from root's checked `WordToStack` native caps
at the guest gap 6. A compiled Loop expression keeps its shape in Word, so the
price of an assignment is a structural function of the Loop expression. All
constants live here; the transfer proofs use them only through `LoopPrice`. -/

mutual
  /-- Native cap of evaluating an expression into a destination: var 14,
  constant 19, global or heap lookup 14, load 21 + address, binary operator 28
  per extra operand + operands, shift 32 + operands. -/
  def nativeExpPrice : HolLoopExp 64 → Nat
    | .const _ => 19
    | .var _ => 14
    | .lookup _ => 14
    | .baseAddr => 14
    | .topAddr => 28 + 14 + (32 + 14 + 19)
    | .load address => 21 + nativeExpPrice address
    | .op _ args => 28 * (args.length - 1) + nativeExpsPrice args
    | .shift _ left right => 32 + nativeExpPrice left + nativeExpPrice right
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def nativeExpsPrice : List (HolLoopExp 64) → Nat
    | [] => 0
    | e :: es => nativeExpPrice e + nativeExpsPrice es
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Native leaf caps of the non-recursive Loop statements. -/
def nativeLeafPrice : HolLoopProg 64 → Option Nat
  | .skip | .fail => some 0
  | .tick => some 7
  | .assign _ value => some (nativeExpPrice value)
  | .store address _ => some (21 + 14 + nativeExpPrice address)
  | .setGlobal _ value => some (14 + nativeExpPrice value)
  | .shMem _ _ address => some (21 + 14 + nativeExpPrice address)
  | .load32 _ _ | .loadByte _ _ | .store32 _ _ | .storeByte _ _ => some (21 + 14)
  | .arith _ => some 43
  | .primitive _ _ _ => some (14 + 43 + 14 + 14)
  | .break _ | .continue _ => some 7
  | .raise _ => some 63
  | .return values => some (15 + 28 * values.length)
  | .locValue _ _ => some 15
  | .ffi _ _ _ _ _ _ => some 25
  | _ => none

/-- Native-calibrated Loop prices: conditional `I + T = 30 + 7`, loop iteration
`2T + L = 16`, call base 189 (handler push/pop, frame, liveness), 39 per
spilled argument, 21 + 28 per returned word, and the continuation tick 7. -/
def nativeLoopPrice : LoopPrice where
  leaf := nativeLeafPrice
  ite := 37
  iter := 16
  call := 189
  arg := 39
  ret := 49
  cont := 7

#print axioms nativeLoopPrice
end InitECandidate.Runtime.FineCost
