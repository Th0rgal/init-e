import InitECandidate.Runtime.CompactNibbleAllocationWordFrame
import InitECandidate.Runtime.CompactNibbleByteScope
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem compact_nibble_odd_scope_returned_word_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap c0 first watched : BitVec 64)
    (positive : 0 < length.toNat) (inputBound : length.toNat ≤ 134217712)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atc0 : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atfirst : s.locals.lookup (ofString "first") = some (.val (.word first)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleOddScope = (some (.returned value),post)) :
    post.memory watched = s.memory watched := by
  rw [source_compactNibble_odd_scope] at run
  obtain ⟨iv,output,initialized,child,final⟩ := evaluate_dec_returned_scope s post
    (ofString "odd") _ _ _ value run
  have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [.var .local (ofString "first"),.const 1]) = some (.val (.word (first &&& 1))) := by
    simp [evalHOLExact,evalListHOLExact,atfirst,wordOpHOL,wordOp,valueIsWord,valueWord]
    change first &&& ((1 : BitVec 64) &&& 18446744073709551615) = _
    bv_decide
  rw [evaluated] at initialized
  cases initialized
  have frame := compact_nibble_allocate_returned_word_frame (setVarHOLFinite (ofString "odd") _ s) output
    pointer length heap c0 (first &&& 1) watched positive inputBound
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "p" by decide] using atPointer)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "n" by decide] using atLength)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "c0" by decide] using atc0)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    code atHeap heapBound below value child
  rw [final]
  exact frame

#print axioms compact_nibble_odd_scope_returned_word_frame

theorem compact_nibble_leaf_scope_returned_word_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap c0 first watched : BitVec 64)
    (positive : 0 < length.toNat) (inputBound : length.toNat ≤ 134217712)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atc0 : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atfirst : s.locals.lookup (ofString "first") = some (.val (.word first)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleLeafScope = (some (.returned value),post)) :
    post.memory watched = s.memory watched := by
  rw [source_compactNibble_leaf_scope] at run
  obtain ⟨iv,output,initialized,child,final⟩ := evaluate_dec_returned_scope s post
    (ofString "is_leaf") _ _ _ value run
  have frame := compact_nibble_odd_scope_returned_word_frame (setVarHOLFinite (ofString "is_leaf") _ s) output
    pointer length heap c0 first watched positive inputBound
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "p" by decide] using atPointer)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "n" by decide] using atLength)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "c0" by decide] using atc0)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "first" by decide] using atfirst)
    code atHeap heapBound below value child
  rw [final]
  exact frame

#print axioms compact_nibble_leaf_scope_returned_word_frame

theorem compact_nibble_first_scope_returned_word_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap c0 watched : BitVec 64)
    (positive : 0 < length.toNat) (inputBound : length.toNat ≤ 134217712)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atc0 : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleFirstScope = (some (.returned value),post)) :
    post.memory watched = s.memory watched := by
  rw [source_compactNibble_first_scope] at run
  obtain ⟨iv,output,initialized,child,final⟩ := evaluate_dec_returned_scope s post
    (ofString "first") _ _ _ value run
  have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.shift .lsr (.var .local (ofString "c0")) (.const 4)) = some (.val (.word (c0 >>> (4 : Nat)))) := by
    simp [evalHOLExact,atc0,wordShiftHOL]
  rw [evaluated] at initialized
  cases initialized
  have frame := compact_nibble_leaf_scope_returned_word_frame (setVarHOLFinite (ofString "first") _ s) output
    pointer length heap c0 (c0 >>> (4 : Nat)) watched positive inputBound
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "p" by decide] using atPointer)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "n" by decide] using atLength)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "c0" by decide] using atc0)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    code atHeap heapBound below value child
  rw [final]
  exact frame

#print axioms compact_nibble_first_scope_returned_word_frame

theorem compact_nibble_byte_scope_returned_word_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap  watched : BitVec 64)
    (positive : 0 < length.toNat) (inputBound : length.toNat ≤ 134217712)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (below : watched.toNat < (panByteAlignHOL heap).toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s compactNibbleByteScope = (some (.returned value),post)) :
    post.memory watched = s.memory watched := by
  rw [source_compactNibble_byte_scope] at run
  obtain ⟨iv,output,initialized,child,final⟩ := evaluate_dec_returned_scope s post
    (ofString "c0") _ _ _ value run
  cases loaded : @panMemLoadByteHOL 64 _ s.memory s.memaddrs
      (fun address => Classical.propDecidable (s.memaddrs address)) s.be pointer with
  | none => simp [evalHOLExact,atPointer,loaded] at initialized
  | some byte =>
    have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
      simp [evalHOLExact,atPointer,loaded]
    rw [evaluated] at initialized
    cases initialized
    have frame := compact_nibble_first_scope_returned_word_frame (setVarHOLFinite (ofString "c0") _ s) output
      pointer length heap (BitVec.ofNat 64 byte.toNat) watched positive inputBound
      (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "c0" ≠ ofString "p" by decide] using atPointer)
      (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "c0" ≠ ofString "n" by decide] using atLength)
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      code atHeap heapBound below value child
    rw [final]
    exact frame

#print axioms compact_nibble_byte_scope_returned_word_frame
end InitECandidate.Runtime
