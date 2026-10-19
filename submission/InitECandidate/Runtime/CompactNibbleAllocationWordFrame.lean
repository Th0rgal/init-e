import InitECandidate.Runtime.CompactNibbleAllocate
import InitECandidate.Runtime.CompactNibbleOutputWordFrame
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem byte_interval_separate_below_aligned (heap watched : BitVec 64) (size : Nat)
    (fits : heap.toNat + size ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat) :
    ∀ offset : Nat, offset < size → watched ≠ panByteAlignHOL (heap + BitVec.ofNat 64 offset) := by
  intro offset inside same
  have offsetBound : offset < 2^64 := by omega
  have sumBound : heap.toNat + offset < 2^64 := by omega
  have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
    rw [BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt offsetBound,Nat.mod_eq_of_lt sumBound]
  have equal := congrArg BitVec.toNat same
  rw [panByteAlign_toNat64,addNat] at equal
  rw [panByteAlign_toNat64] at below
  have monotone := Nat.mul_le_mul_right 8
    (Nat.div_le_div_right (show heap.toNat ≤ heap.toNat + offset by omega) :
      heap.toNat / 8 ≤ (heap.toNat + offset) / 8)
  omega

/-- The actual returned allocator call supplies the output allocation bound.
No successful allocation, room, or byte-domain premise is supplied by callers. -/
theorem compact_nibble_allocate_returned_word_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap c0 odd watched : BitVec 64)
    (positive : 0 < length.toNat) (inputBound : length.toNat ≤ 134217712)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleAllocate = (some (.returned value),post)) :
    post.memory watched = s.memory watched := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.const 2,.var .local (ofString "n")]] = some [.val (.word (2 * length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
  rw [source_compactNibble_allocate] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "out")
      (.panop .mul [.const 2,.var .local (ofString "n")]) compactNibbleAfterAlloc heap (2 * length) value
      args code atHeap heapBound run
  have sizeNat : (2 * length).toNat = 2 * length.toNat := by
    rw [BitVec.toNat_mul]
    change (2 * length.toNat) % 2^64 = 2 * length.toNat
    exact Nat.mod_eq_of_lt (by omega)
  have fits : heap.toNat + 2 * length.toNat ≤ 33806089496 := by
    rw [sizeNat] at covers
    omega
  have other : ∀ name, name ≠ ofString "out" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atOut : ready.locals.lookup (ofString "out") = some (.val (.word heap)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have frame := compact_nibble_after_alloc_word_frame ready pointer length heap c0 odd watched positive (by omega)
    ((other _ (by decide)).trans atPointer) ((other _ (by decide)).trans atLength) atOut
    ((other _ (by decide)).trans atByte) ((other _ (by decide)).trans atOdd) (readyCode.trans code)
    (byte_interval_separate_below_aligned heap watched (2 * length.toNat) fits below)
  rw [tailRun] at frame
  dsimp only at frame
  exact (congrFun postMemory watched).trans (frame.trans (congrFun memory watched))

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.byte_interval_separate_below_aligned
#print axioms InitECandidate.Runtime.compact_nibble_allocate_returned_word_frame
