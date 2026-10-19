import InitECandidate.Runtime.DecodeStepCompactTableBound
import InitECandidate.Runtime.DecodeStepFirstItemReach
import InitECandidate.Runtime.DecodeStepLeafValueUniformBound
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepTwoCaseCost (limit : Nat) : Nat :=
  (limit*((2*limit+1)*15+19)+92633) +
    (1 + ((limit/4+7) + (limit*((2*limit+1)*15+19)+92637)))

/-- Both actual RLP item parses and compact-path conversion are bounded using
only the original input cap. The second table entry survives the first parse
and the real compact output writes; failed accesses/allocation are included. -/
theorem runBounded_decode_step_two_case {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array firstPointer firstLength secondPointer secondLength heap scratch frame : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (first : RlpSliceEntry s array 0 firstPointer firstLength)
    (second : RlpSliceEntry s array 1 secondPointer secondLength)
    (firstNoWrap : firstPointer.toNat + firstLength.toNat < 2^64)
    (secondNoWrap : secondPointer.toNat + secondLength.toNat < 2^64)
    (firstBound : firstLength.toNat ≤ inputLimit) (secondBound : secondLength.toNat ≤ inputLimit)
    (inputBound : inputLimit ≤ 134217712)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (tableBefore : array.toNat + 32 ≤ heap.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepTwoCaseCost inputLimit ≤ s.clock) :
    RunBounded s decodeStepTwoCase (decodeStepTwoCaseCost inputLimit) := by
  have firstProduct : firstLength.toNat*((2*firstLength.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
    Nat.mul_le_mul firstBound (by omega)
  have secondProduct : secondLength.toNat*((2*secondLength.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
    Nat.mul_le_mul secondBound (by omega)
  have firstReach :=  decode_step_first_item_reaches s array firstPointer firstLength scratch frame ceiling inputLimit
    atArray first firstNoWrap firstBound (by omega) scratchGlobal frameGlobal code ordered framePositive scratchBelow arena
    ((Nat.add_le_add_right firstProduct 92633).trans ((Nat.le_add_right _ _).trans budget))
  have actualBudget : (firstLength.toNat*((2*firstLength.toNat+1)*15+19)+92633) +
      (1 + ((inputLimit/4+7)+(inputLimit*((2*inputLimit+1)*15+19)+92637))) ≤ s.clock := by
    exact (Nat.add_le_add_right (Nat.add_le_add_right firstProduct 92633) _).trans budget
  have whole := RunBounded.ofReaches actualBudget firstReach (by
    intro next facts ticks
    obtain ⟨kind,pp,payload,consumed,atItem,_,_,_,payloadBound,scratchNext,frameNext,heapNext,
      codeNext,domain,locals,memory⟩ := facts
    have arrayNext : next.locals.lookup (ofString "arr") = some (.val (.word array)) := by
      rw [locals]
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pi" ≠ ofString "arr" by decide] using atArray
    have pnat : (array + 16#64).toNat = array.toNat + 16 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+16 < 2^64; omega)]
      rfl
    have lnat : (array + 24#64).toNat = array.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat+24 < 2^64; omega)]
      rfl
    have secondNext := RlpSliceEntry.after_frame s next array 1 secondPointer secondLength second domain
      (memory _ (by rw [show (1 : BitVec 64)*16#64 = 16#64 from by decide,pnat]; omega))
      (memory _ (by rw [show (1 : BitVec 64)*16#64 = 16#64 from by decide,BitVec.add_assoc,
        show (16#64+8#64) = 24#64 from by decide,lnat]; omega))
    have divided : payload.toNat / 4 ≤ inputLimit / 4 := Nat.div_le_div_right (payloadBound.trans firstBound)
    rw [source_decode_step_first_item_guard]
    apply RunBounded.seq (b := (inputLimit/4+7)+(inputLimit*((2*inputLimit+1)*15+19)+92637))
      (RunBounded.ofProg (mpt_fail_guard_uniform_bounded _ 5) (codeNext.trans code) (by omega)) ticks
    intro guarded normal guardedCode tailTicks
    have same := mpt_fail_guard_normal_state next guarded _ 5 (codeNext.trans code) normal
    subst guarded
    have compact := runBounded_decode_step_compact_table_call next kind pp payload consumed array secondPointer secondLength
      heap scratch frame atItem arrayNext secondNext (heapNext.trans atHeap) heapBound aligned tableBefore (by omega)
      scratchNext frameNext (codeNext.trans code) ceiling inputLimit secondNoWrap secondBound (by omega) ordered framePositive
      scratchBelow (by intro address lower upper; rw [domain]; exact arena address lower upper)
      ((Nat.add_le_add (Nat.add_le_add_right divided 7) (Nat.add_le_add_right secondProduct 92637)).trans tailTicks)
    exact compact.weaken (Nat.add_le_add (Nat.add_le_add_right divided 7) (Nat.add_le_add_right secondProduct 92637)))
  exact whole.weaken (Nat.add_le_add_right (Nat.add_le_add_right firstProduct 92633) _)

#print axioms runBounded_decode_step_two_case
end InitECandidate.Runtime
