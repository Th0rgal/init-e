import InitECandidate.Runtime.CompactNibbleScopesUniformBound
import InitECandidate.Runtime.CompactNibbleEmptyBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_compact_nibble_byte_scope {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 6 ≤ s.clock) :
    RunBounded s compactNibbleByteScope ((length - 1).toNat / 4 + 6) := by
  rw [source_compactNibble_byte_scope]
  apply RunBounded.dec
  intro value evaluated
  cases loaded : @panMemLoadByteHOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be pointer with
  | none => simp [evalHOLExact,atPointer,loaded] at evaluated
  | some byte =>
    have valueEq : value = .val (.word (BitVec.ofNat 64 byte.toNat)) := by
      simpa [evalHOLExact,atPointer,loaded] using evaluated.symm
    subst value
    apply runBounded_compact_nibble_first_scope _ pointer length (BitVec.ofNat 64 byte.toNat) small
    · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "c0" ≠ ofString "p" by decide] using atPointer
    · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "c0" ≠ ofString "n" by decide] using atLength
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · exact code
    · exact ticks

/-- Complete original compact-path decoder bound, including empty input,
inaccessible bytes, allocator rejection and failed output stores. -/
theorem runBounded_compact_nibble_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (small : length.toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode) (ticks : length.toNat / 4 + 6 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_compact_to_nibbles) (length.toNat / 4 + 6) := by
  by_cases zero : length = 0
  · subst length
    have empty := evaluate_compactNibble_empty_body s atLength code (by omega)
    exact ⟨by rw [empty.1]; omega,by rw [empty.1]; omega,empty.2.1⟩
  · have positive : 0 < length.toNat := by
      by_contra h
      apply zero
      apply BitVec.eq_of_toNat_eq
      simpa using (show length.toNat = 0 by omega)
    have subNat : (length - 1).toNat = length.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ length.toNat; omega)]
      rfl
    have divided : (length - 1).toNat / 4 ≤ length.toNat / 4 :=
      Nat.div_le_div_right (by rw [subNat]; omega)
    have bounded := runBounded_compact_nibble_byte_scope s pointer length (by rw [subNat]; omega)
      atPointer atLength code (by omega)
    have guard : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
          (.call (some (none,none)) (ofString "mpt_fail") [.const 5]) .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL,
        show length ≠ 0#64 from zero,evaluateHOLFiniteState_skip]
    unfold RunBounded
    rw [source_compactNibble_body,evaluateHOLFiniteState_seq_line780,guard]
    exact bounded.weaken (by omega)

#print axioms runBounded_compact_nibble_byte_scope
#print axioms runBounded_compact_nibble_body
end InitECandidate.Runtime
