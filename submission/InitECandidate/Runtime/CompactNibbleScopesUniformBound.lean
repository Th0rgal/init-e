import InitECandidate.Runtime.CompactNibbleAllocateUniformBound
import InitECandidate.Runtime.CompactNibbleByteScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_compact_nibble_odd_scope {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length c0 first : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atFirst : s.locals.lookup (ofString "first") = some (.val (.word first)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 6 ≤ s.clock) :
    RunBounded s compactNibbleOddScope ((length - 1).toNat / 4 + 6) := by
  rw [source_compactNibble_odd_scope]
  have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [.var .local (ofString "first"),.const 1]) = some (.val (.word (first &&& 1))) := by
    simp [evalHOLExact,evalListHOLExact,atFirst,wordOpHOL,wordOp,valueIsWord,valueWord]
    change first &&& ((1 : BitVec 64) &&& 18446744073709551615) = _
    bv_decide
  apply RunBounded.decWord s (ofString "odd") _ (first &&& 1) evaluated
  apply runBounded_compact_nibble_allocate _ pointer length c0 (first &&& 1) small
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "p" by decide] using atPointer
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "n" by decide] using atLength
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "odd" ≠ ofString "c0" by decide] using atByte
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact code
  · exact ticks

theorem runBounded_compact_nibble_leaf_scope {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length c0 first : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atFirst : s.locals.lookup (ofString "first") = some (.val (.word first)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 6 ≤ s.clock) :
    RunBounded s compactNibbleLeafScope ((length - 1).toNat / 4 + 6) := by
  rw [source_compactNibble_leaf_scope]
  apply RunBounded.dec
  intro value evaluated
  apply runBounded_compact_nibble_odd_scope _ pointer length c0 first small
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "p" by decide] using atPointer
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "n" by decide] using atLength
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "c0" by decide] using atByte
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "is_leaf" ≠ ofString "first" by decide] using atFirst
  · exact code
  · exact ticks

theorem runBounded_compact_nibble_first_scope {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length c0 : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 6 ≤ s.clock) :
    RunBounded s compactNibbleFirstScope ((length - 1).toNat / 4 + 6) := by
  rw [source_compactNibble_first_scope]
  apply RunBounded.decWord s (ofString "first") _ (c0 >>> (4 : Nat))
    (by simp [evalHOLExact,atByte,wordShiftHOL])
  apply runBounded_compact_nibble_leaf_scope _ pointer length c0 (c0 >>> (4 : Nat)) small
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "p" by decide] using atPointer
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "n" by decide] using atLength
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "first" ≠ ofString "c0" by decide] using atByte
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact code
  · exact ticks

#print axioms runBounded_compact_nibble_odd_scope
#print axioms runBounded_compact_nibble_leaf_scope
#print axioms runBounded_compact_nibble_first_scope
end InitECandidate.Runtime
