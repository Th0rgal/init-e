import InitECandidate.Runtime.MerklePositiveBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleEmptyCheck : ProgHOL 64 :=
  match merkleizeAt 3 with | .seq first _ => first | _ => .skip

def merkleEmptyBranch : ProgHOL 64 :=
  match merkleEmptyCheck with | .ite _ yes _ => yes | _ => .skip

theorem source_merkleEmpty_check : merkleEmptyCheck =
    .ite (.cmp .equal (.var .local (ofString "n")) (.const (0#64))) merkleEmptyBranch .skip := by rfl

theorem source_merkleEmpty_branch : merkleEmptyBranch =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "out"),
       .op .add [.var .global (ofString "zero_hashes"),.panop .mul [.var .local (ofString "target"),.const 32]],
       .const 32]) (.return (.const 0)) := by rfl

theorem source_merkleEmpty_sequence : merkleizeAt 3 = .seq merkleEmptyCheck (merkleizeAt 4) := by rfl

theorem merkleEmpty_branch_bounded : ProgBounded merkleEmptyBranch 16 := by
  rw [source_merkleEmpty_branch]
  exact ProgBounded.seq (memcpy_const_progBounded _ _ 32 (by decide)) (ProgBounded.straight _ (by decide))

theorem merkleEmpty_check_bounded : ProgBounded merkleEmptyCheck 16 := by
  rw [source_merkleEmpty_check]
  exact ProgBounded.ite _ merkleEmpty_branch_bounded
    (ProgBounded.weaken (ProgBounded.straight _ (by decide)) (Nat.zero_le _))

theorem merkleEmpty_branch_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state merkleEmptyBranch).1 ≠ none := by
  rw [source_merkleEmpty_branch]
  exact evaluate_seq_terminal state _ _ (fun current => evaluate_return_terminal current _)

/-- Only the nonempty branch can fall through, and that branch leaves the
entire caller state unchanged. -/
theorem merkleEmpty_check_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (run : evaluateHOLFiniteState state merkleEmptyCheck = (none,post)) : post = state := by
  rw [source_merkleEmpty_check,evaluateHOLFiniteState_ite] at run
  by_cases zero : n = (0#64)
  · have branchRun : evaluateHOLFiniteState state merkleEmptyBranch = (none,post) := by
      simpa [evalHOLExact,count,Compiler.Encoders.Asm.wordCmpHOL,zero] using run
    have terminal := merkleEmpty_branch_terminal state
    rw [branchRun] at terminal
    exact False.elim (terminal rfl)
  · have equal : ((none : Option (PanSemResultExact 64)),state) = (none,post) := by
      simpa [evalHOLExact,count,Compiler.Encoders.Asm.wordCmpHOL,zero,evaluateHOLFiniteState_skip] using run
    exact (Prod.mk.inj equal).2.symm

def merkleAfterTargetCost : Nat := 16 + merklePositiveCost

/-- Both actual count cases are covered: empty input returns after the fixed
copy; nonempty input enters the bounded allocation/hashing branch. -/
theorem runBounded_merkleAfterTarget {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n dn target heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n ((1#64) <<< dn.toNat))
    (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleAfterTargetCost ≤ state.clock) :
    RunBounded state (merkleizeAt 3) merkleAfterTargetCost := by
  rw [source_merkleEmpty_sequence]
  refine RunBounded.seq (RunBounded.ofProg merkleEmpty_check_bounded code
    (by unfold merkleAfterTargetCost at budget; omega)) budget ?_
  intro next run _ remaining
  have same := merkleEmpty_check_normal state next n count run
  subst next
  exact runBounded_merklePositive state pointer n dn target heap input count depth limit lengths
    depthBound targetBound heapLocal heapBound code remaining

#print axioms source_merkleEmpty_check
#print axioms source_merkleEmpty_branch
#print axioms source_merkleEmpty_sequence
#print axioms merkleEmpty_branch_bounded
#print axioms merkleEmpty_check_bounded
#print axioms merkleEmpty_branch_terminal
#print axioms merkleEmpty_check_normal
#print axioms runBounded_merkleAfterTarget
end InitECandidate.Runtime
