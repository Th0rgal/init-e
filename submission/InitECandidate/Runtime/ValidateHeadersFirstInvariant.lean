import InitECandidate.Runtime.ValidateHeadersFirstBodyNormalFrame
import InitECandidate.Runtime.ValidateHeadersFirstLocalFrame
import InitECandidate.Runtime.ValidateHeadersFirstCondition
import InitECandidate.Runtime.ValidateHeadersFirstControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed geometry and input parameters for the first actual validation loop. -/
structure ValidateHeadersFirstEnvironment where
  array : BitVec 64
  count : BitVec 64
  input : BitVec 64
  inputLength : BitVec 64
  scratch : BitVec 64
  frame : BitVec 64
  hs : BitVec 64
  hashes : BitVec 64
  keccakState : BitVec 64
  keccakPad : BitVec 64
  ceiling : Nat
  inputLimit : Nat
  cap : count.toNat ≤ 256
  inputBound : inputLength.toNat ≤ inputLimit
  inputCap : inputLimit ≤ 134217712
  inputAfter : ceiling ≤ input.toNat
  tableAbove : ceiling ≤ array.toNat
  tableBeforeHs : array.toNat + count.toNat * 16 ≤ hs.toNat
  hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496
  hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496
  hashAligned : hashes.toNat % 8 = 0
  hsBeforeHashes : hs.toNat ≤ hashes.toNat
  orderedFrame : frame ≤ scratch
  framePositive : 0 < frame.toNat
  scratchBelow : scratch.toNat ≤ ceiling
  ceilingAligned : ceiling % 8 = 0
  stateBelow : keccakState.toNat + 200 ≤ ceiling
  padBelow : keccakPad.toNat + 136 ≤ ceiling

/-- The real witness, dynamic allocation frontier and caller-local counter
needed to apply the already checked iteration contracts. Clock is deliberately
absent so the invariant also holds after the while tick. -/
def ValidateHeadersFirstInvariant {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ index heap : BitVec 64,
    s.locals.lookup (ofString "arr") = some (.val (.word e.array)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word e.count)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    s.locals.lookup (ofString "hs") = some (.val (.word e.hs)) ∧
    s.locals.lookup (ofString "hashes") = some (.val (.word e.hashes)) ∧
    index.toNat ≤ e.count.toNat ∧ rank = e.count.toNat - index.toNat ∧
    RlpSliceInputPrefix s e.array e.input e.inputLength e.count.toNat ∧
    e.input.toNat + e.inputLength.toNat ≤ heap.toNat ∧
    e.array.toNat + e.count.toNat * 16 ≤ heap.toNat ∧
    s.globals.lookup (ofString "scratch_ptr") = some (.val (.word e.scratch)) ∧
    s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word e.frame)) ∧
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    s.globals.lookup (ofString "keccak_st") = some (.val (.word e.keccakState)) ∧
    s.globals.lookup (ofString "keccak_pad") = some (.val (.word e.keccakPad)) ∧
    heap.toNat ≤ 33806089496 ∧
    (∀ address : BitVec 64, e.frame.toNat ≤ address.toNat → address.toNat < e.ceiling → s.memaddrs address) ∧
    (∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)

/-- The while tick changes only clock, leaving the real invariant intact. -/
theorem validate_headers_first_invariant_dec_clock {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat)
    (valid : ValidateHeadersFirstInvariant e s rank) :
    ValidateHeadersFirstInvariant e (decClockHOLFinite s) rank := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,rest⟩ := valid
  refine ⟨index,heap,arr,n,i,hs,hashes,within,distance,?_,rest⟩
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := table slot inside
  exact ⟨pointer,length,entry.after_frame s (decClockHOLFinite s) e.array slot pointer length e.input e.inputLength rfl rfl rfl⟩

/-- A zero rank makes the actual signed condition false under the invariant. -/
theorem validate_headers_first_invariant_exit {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (valid : ValidateHeadersFirstInvariant e s 0) (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w))) :
    w = 0 := by
  obtain ⟨index,heap,atArray,atCount,atIndex,atHs,atHashes,within,distance,rest⟩ := valid
  exact validate_headers_first_condition_rank_zero s index e.count w e.cap within atIndex atCount distance.symm condition

#print axioms validate_headers_first_invariant_dec_clock
#print axioms validate_headers_first_invariant_exit
end InitECandidate.Runtime
