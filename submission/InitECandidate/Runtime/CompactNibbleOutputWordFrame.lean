import InitECandidate.Runtime.KeyNibbleBodyWordFrame
import InitECandidate.Runtime.CompactNibbleAfterAllocUniformBound
import InitECandidate.Runtime.ByteStoreChainFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem compact_nibble_prefix_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out odd watched : BitVec 64)
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (separate : watched ≠ panByteAlignHOL out) :
    (evaluateHOLFiniteState s compactNibblePrefix).2.memory watched = s.memory watched := by
  have chain : ByteStoreChainFrame (F := F) s.locals watched
      (.seq (.storeByte (.var .local (ofString "out"))
        (.op .and [.var .local (ofString "c0"),.const 15]))
        (.assign .local (ofString "k") (.const 1))) := by
    apply ByteStoreChainFrame.store
    · intro current same
      exact ⟨out,by simpa only [evalHOLExact,same] using atOut,separate⟩
    · exact ByteStoreChainFrame.tail _ rfl
  have stored := evaluate_byteStoreChain_frame chain s rfl
  rw [source_compactNibble_prefix,evaluateHOLFiniteState_ite]
  by_cases zero : odd = 0
  · simp [evalHOLExact,atOdd,Compiler.Encoders.Asm.wordCmpHOL,zero,evaluateHOLFiniteState_skip]
  · have guard : @evalHOLExact 64 F _ s.toExact
        (fun address => Classical.propDecidable (s.memaddrs address))
        (.cmp .notEqual (.var .local (ofString "odd")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,atOdd,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [guard]
    simpa only [show (1 : BitVec 64) ≠ 0 from by decide,reduceIte] using stored

theorem compact_nibble_finish_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length out initial watched : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atCounter : s.locals.lookup (ofString "k") = some (.val (.word initial)))
    (code : s.code = originalRuntimeCode)
    (separate : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      watched ≠ panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s compactNibbleFinish).2.memory watched = s.memory watched := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      compactNibbleArguments = some [.val (.word (pointer + 1)),.val (.word (length - 1)),.val (.word (out + initial))] := by
    simp [compactNibbleArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      atPointer,atLength,atOut,atCounter,wordOpHOL,wordOp,valueIsWord,valueWord]
  have frame := evaluate_keyNibble_call_word_frame s _ _ _ (pointer + 1) (length - 1) (out + initial) watched
    small code args separate
  change (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles") compactNibbleArguments)).2.memory watched = s.memory watched at frame
  rw [← source_compactNibble_conversion] at frame
  rw [source_compactNibble_finish,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState s compactNibbleConversion with
  | mk result middle =>
    rw [run] at frame
    dsimp only at frame ⊢
    cases result with
    | some stopped => exact frame
    | none =>
      exact (congrFun (evaluate_readOnly_memory _ rfl middle) watched).trans frame

/-- Actual post-allocation decoder memory frame, without successful byte
accesses, sufficient fuel, or a successful return being assumed. -/
theorem compact_nibble_after_alloc_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length out c0 odd watched : BitVec 64)
    (positive : 0 < length.toNat) (small : length.toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (code : s.code = originalRuntimeCode)
    (separate : ∀ offset : Nat, offset < 2 * length.toNat →
      watched ≠ panByteAlignHOL (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s compactNibbleAfterAlloc).2.memory watched = s.memory watched := by
  have subNat : (length - 1).toNat = length.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ length.toNat; omega)]
    rfl
  let entered := setVarHOLFinite (ofString "k") (.val (.word (0#64))) s
  have other : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atK : entered.locals.lookup (ofString "k") = some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have firstSeparate : watched ≠ panByteAlignHOL out := by
    simpa using separate 0 (by omega)
  have prefixFrame := compact_nibble_prefix_word_frame entered out odd watched
    ((other _ (by decide)).trans atOut) ((other _ (by decide)).trans atOdd) firstSeparate
  rw [source_compactNibble_after_alloc,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (evaluateHOLFiniteState entered (.seq compactNibblePrefix compactNibbleFinish)).2.memory watched = s.memory watched
  rw [evaluateHOLFiniteState_seq_line780]
  cases prefixRun : evaluateHOLFiniteState entered compactNibblePrefix with
  | mk result middle =>
    rw [prefixRun] at prefixFrame
    dsimp only at prefixFrame ⊢
    cases result with
    | some stopped => exact prefixFrame
    | none =>
      obtain ⟨counter,locals⟩ := compact_nibble_prefix_normal_frame entered middle out c0 odd
        ((other _ (by decide)).trans atOut) ((other _ (by decide)).trans atByte)
        ((other _ (by decide)).trans atOdd) atK prefixRun
      let initial : BitVec 64 := if odd = 0 then 0 else 1
      have initialSmall : initial.toNat ≤ 1 := by
        dsimp only [initial]
        split <;> decide
      have conversionSeparate : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
          watched ≠ panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset) := by
        intro offset inside
        have address : initial + BitVec.ofNat 64 offset = BitVec.ofNat 64 (initial.toNat + offset) := by
          simp [BitVec.ofNat_add]
        rw [BitVec.add_assoc,address]
        exact separate _ (by rw [subNat] at inside; omega)
      have metadata := evaluateHOLFiniteState_metadata entered compactNibblePrefix
      rw [prefixRun] at metadata
      have finish := compact_nibble_finish_word_frame middle pointer length out initial watched
        (by rw [subNat]; omega)
        ((locals _ (by decide)).trans ((other _ (by decide)).trans atPointer))
        ((locals _ (by decide)).trans ((other _ (by decide)).trans atLength))
        ((locals _ (by decide)).trans ((other _ (by decide)).trans atOut)) counter
        (metadata.1.trans code) conversionSeparate
      exact finish.trans prefixFrame

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.compact_nibble_prefix_word_frame
#print axioms InitECandidate.Runtime.compact_nibble_finish_word_frame
#print axioms InitECandidate.Runtime.compact_nibble_after_alloc_word_frame
