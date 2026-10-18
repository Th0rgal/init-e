import InitECandidate.Runtime.Sha256UnpackSource
import InitECandidate.Runtime.ArithmeticExpressionWord
import InitECandidate.Runtime.WatchedMemoryComposition
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockUnpack_low_word {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      shaBlockUnpackLow = some value) : ∃ word : BitVec 64, value = .val (.word word) :=
  eval_shift_returns_word state .lsr _ _ value evaluated

theorem shaBlockUnpack_high_word {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      shaBlockUnpackHigh = some value) : ∃ word : BitVec 64, value = .val (.word word) :=
  eval_shift_returns_word state .lsr _ _ value evaluated

theorem shaBlockUnpack_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index pointer watched : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (small : index.toNat < 4) (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat) :
    (evaluateHOLFiniteState state shaBlockUnpackBody).2.memory watched = state.memory watched := by
  have mulNatural : (index * (16#64)).toNat = index.toNat * 16 :=
    BitVec.toNat_mul_of_lt (by change index.toNat * 16 < 2 ^ 64; omega)
  have addressNatural : (pointer + index * (16#64)).toNat = pointer.toNat + index.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [mulNatural]; omega),mulNatural]
  have highNatural : (pointer + index * (16#64) + (8#64)).toNat = pointer.toNat + index.toNat * 16 + 8 := by
    rw [BitVec.toNat_add_of_lt (by change (pointer + index * (16#64)).toNat + 8 < 2 ^ 64; rw [addressNatural]; omega),addressNatural]
    rfl
  have lowSeparate : watched ≠ pointer + index * (16#64) := by
    intro same
    have natural := congrArg BitVec.toNat same
    rw [addressNatural] at natural
    rcases outside with before | after <;> omega
  have highSeparate : watched ≠ pointer + index * (16#64) + (8#64) := by
    intro same
    have natural := congrArg BitVec.toNat same
    rw [highNatural] at natural
    rcases outside with before | after <;> omega
  rw [source_shaBlock_unpack_body]
  apply watched_memory_dec
  intro packed
  let entered := setVarHOLFinite (ofString "packed") packed state
  have indexLocal : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atIndex
  have pointerLocal : entered.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer
  apply watched_memory_seq
  · apply evaluate_wordStore_memory_frame entered _ _ (pointer + index * (16#64)) watched
    · simp [shaBlockUnpackAddress,evalHOLExact,evalListHOLExact,indexLocal,pointerLocal,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
    · exact fun parsed evaluated => shaBlockUnpack_low_word entered parsed evaluated
    · exact lowSeparate
  · intro next normal
    have locals := (evaluate_store_control_frame entered shaBlockUnpackAddress shaBlockUnpackLow).2.1
    rw [normal] at locals
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word index)) := by rw [locals]; exact indexLocal
    have nextPointer : next.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by rw [locals]; exact pointerLocal
    apply watched_memory_seq
    · apply evaluate_wordStore_memory_frame next _ _ (pointer + index * (16#64) + (8#64)) watched
      · simp [evalHOLExact,evalListHOLExact,nextIndex,nextPointer,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,BitVec.add_assoc]
      · exact fun parsed evaluated => shaBlockUnpack_high_word next parsed evaluated
      · exact highSeparate
    · intro final normal
      exact congrFun (evaluate_readOnly_memory _ rfl final) watched

#print axioms shaBlockUnpack_low_word
#print axioms shaBlockUnpack_high_word
#print axioms shaBlockUnpack_body_memory
end InitECandidate.Runtime
