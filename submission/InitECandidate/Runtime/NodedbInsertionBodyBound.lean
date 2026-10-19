import InitECandidate.Runtime.NodedbInsertionHash
import InitECandidate.Runtime.KeccakHtabFrame
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- One original database iteration is bounded by hashing plus insertion.
The table invariant is transported through the actual hash execution, rather
than assumed again at the intermediate state. All outcomes are covered. -/
theorem runBounded_nodedb_insertion_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad array index source size output heap : BitVec 64)
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned 32 table keys stride capacity used values order orderPos count bits state)
    (ordered : OrderInv state capacity count used order orderPos)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atArray : state.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atTable : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (atOutput : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (sourceDomain : state.memaddrs (array + index * (16#64)))
    (sizeDomain : state.memaddrs (array + index * (16#64) + (8#64)))
    (sourceCell : state.memory (array + index * (16#64)) = .word source)
    (sizeCell : state.memory (array + index * (16#64) + (8#64)) = .word size)
    (small : size.toNat ≤ 134217712) (outAligned : output.toNat % 8 = 0)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapAligned : heap.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ heap.toNat)
    (heapInside : heap.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat)
    (separate : ∀ watched : BitVec 64, HtabFoot table capacity used order orderPos watched.toNat →
      ¬ MWin pointer 200 watched ∧ ¬ MWin pad 136 watched ∧ ¬ MWin output 32 watched)
    (budget : (size.toNat * 20 + 125) + (setBodyCost 32 capacity count + 1) ≤ state.clock) :
    RunBounded state nodedbInsertionBody ((size.toNat * 20 + 125) + (setBodyCost 32 capacity count + 1)) := by
  have args := eval_nodedb_hash_arguments state array index source size output atArray atIndex atOutput
    sourceDomain sizeDomain sourceCell sizeCell
  have first := runBounded_nodedb_hash state pointer pad array index source size output inv.code atState atPad
    atArray atIndex atOutput sourceDomain sizeDomain sourceCell sizeCell small outAligned (by omega)
  unfold nodedbInsertionBody
  refine RunBounded.seq first budget ?_
  intro next normal nextCode remaining
  have tableFrame := keccak_call_htab_frame state pointer pad source size output nodedbHashArguments
    32 table keys stride capacity used values order orderPos count bits inv ordered atState atPad args small (by omega) separate
  rw [normal] at tableFrame
  have locals := evaluate_discard_call_success_locals state (ofString "keccak256") nodedbHashArguments (by rw [normal])
  rw [normal] at locals
  have globals := keccak_call_globals_frame nodedbHashArguments state inv.code
  rw [normal] at globals
  change next.locals = state.locals at locals
  change next.globals = state.globals at globals
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "keccak256") nodedbHashArguments)
  rw [normal] at metadata
  have setArgs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a)) nodedbSetArguments =
      some [.val (.word table),.val (.word output),.val (.word (array + index * (16#64)))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [nodedbSetArguments,nodedbSliceAddress,evalListHOLExact,evalHOLExact,locals,globals,atTable,atArray,atIndex,atOutput,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have insertion := runBounded_htabSet_call next none _ _ _ 32 table keys stride capacity used values order orderPos count
    output (array + index * (16#64)) heap bits tableFrame.1 setArgs
    (by rw [globals]; exact atHeap) heapAligned headerBelow heapInside
    (by intro a h1 h2 h3; rw [metadata.2.1]; exact arena a h1 h2 h3) room (by decide) remaining
  have whole := RunBounded.seq (tail := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))
    (b := 0) insertion (by omega) (by
      intro post run installed ticks
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (installed.trans (nextCode.trans inv.code)) ticks)
  simpa only [Nat.add_zero,nodedbSetArguments] using whole

#print axioms runBounded_nodedb_insertion_body
end InitECandidate.Runtime
