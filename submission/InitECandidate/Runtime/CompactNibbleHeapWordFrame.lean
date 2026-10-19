import InitECandidate.Runtime.CompactNibbleScopesWordFrame
import InitECandidate.Runtime.CompactNibbleEmptyBody
import InitECandidate.Runtime.MptFailCallTerminal
import InitECandidate.Runtime.AlignedCellDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned actual compact decoder preserves every old heap cell.
For an unaligned frontier the containing word is excluded explicitly. -/
theorem compact_nibble_body_returned_memory_below_aligned {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (inputBound : length.toNat ≤ 134217712)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_compact_to_nibbles) =
      (some (.returned value),post)) :
    ∀ watched, watched.toNat < (panByteAlignHOL heap).toNat → post.memory watched = s.memory watched := by
  have nonzero : length ≠ 0 := by
    intro zero
    subst length
    have check : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
          (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) =
        evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL]
    have terminal := evaluate_mptFail_call_terminal s (.const 5) 5 code (by rfl)
    have noReturn := evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 5] value
    rw [source_compactNibble_body,evaluateHOLFiniteState_seq_line780,check] at run
    cases callRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) with
    | mk result middle =>
      rw [callRun] at terminal noReturn run
      cases result with
      | none => exact terminal rfl
      | some stopped =>
        have equal : some stopped = some (.returned value) := (Prod.mk.inj run).1
        exact noReturn equal
  have positive : 0 < length.toNat := by
    by_contra h
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show length.toNat = 0 by omega)
  have guard : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
        (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) = (none,s) := by
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL,
      show length ≠ 0#64 from nonzero,evaluateHOLFiniteState_skip]
  rw [source_compactNibble_body,evaluateHOLFiniteState_seq_line780,guard] at run
  intro watched below
  exact compact_nibble_byte_scope_returned_word_frame s post pointer length heap watched
    positive inputBound atPointer atLength code atHeap heapBound below value run

/-- Allocator-produced heap frontiers are aligned, so the whole earlier heap
is unchanged by any actual returned compact-path decoder run. -/
theorem compact_nibble_body_returned_memory_below_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (inputBound : length.toNat ≤ 134217712) (aligned : heap.toNat % 8 = 0)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_compact_to_nibbles) =
      (some (.returned value),post)) :
    ∀ watched, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  have frame := compact_nibble_body_returned_memory_below_aligned s post pointer length heap
    atPointer atLength code atHeap heapBound inputBound value run
  simpa only [panByteAlign_eq_self_aligned heap aligned] using frame

#print axioms compact_nibble_body_returned_memory_below_aligned
#print axioms compact_nibble_body_returned_memory_below_heap
end InitECandidate.Runtime
