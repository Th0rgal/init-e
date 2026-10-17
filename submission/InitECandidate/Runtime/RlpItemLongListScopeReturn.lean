import InitECandidate.Runtime.RlpItemLongListBodyReturn
import InitECandidate.Runtime.RlpItemLongListScopeBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongList = (some (.returned value),final)) :
    ∃ payload : BitVec 64,
      value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + (header - 247)))),
        .val (.word payload),.val (.word (1 + ((header - 247) + payload)))] ∧
      payload.toNat < total.toNat ∧
      0 < (1 + ((header - 247) + payload)).toNat ∧
      (1 + ((header - 247) + payload)).toNat ≤ total.toNat := by
  have sizeBound : (header - 247).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ header.toNat; omega)]
    change header.toNat - 247 ≤ 8
    omega
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_long_list] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 247]) (header - 247) rlpItemLongListBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  exact rlpItem_long_list_body_return_contract entered output pointer (header - 247) total value
    atPointer atLength atTotal nonzero code (by change (header - 247).toNat + 2 ≤ state.clock; omega) bodyRun

theorem rlpItem_long_list_after_load_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),final)) :
    ∃ payload : BitVec 64,
      value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + (header - 247)))),
        .val (.word payload),.val (.word (1 + ((header - 247) + payload)))] ∧
      payload.toNat < total.toNat ∧
      0 < (1 + ((header - 247) + payload)).toNat ∧
      (1 + ((header - 247) + payload)).toNat ≤ total.toNat := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have third : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpItemLongString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have fourth : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 247) (.var .local (ofString "b"))) rlpItemShortList .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 247 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,third] at run
  dsimp only at run
  rw [source_rlpItem_list_dispatch,evaluateHOLFiniteState_seq_line780,fourth] at run
  exact rlpItem_long_list_return_contract state final pointer header total value
    pointerLocal headerLocal totalLocal lower upper nonzero code ticks run

#print axioms rlpItem_long_list_return_contract
#print axioms rlpItem_long_list_after_load_return_contract
end InitECandidate.Runtime
