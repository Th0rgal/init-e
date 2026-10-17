import InitECandidate.Runtime.KeyToNibblesGeneralPairAdvance
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One complete original tail iteration establishes two more valid nibbles,
including the source load, declaration scope, writes and counter increment. -/
theorem evaluate_keyToNibbles_tail_range_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out index : BitVec 64) (byte : UInt8)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (key + index) = some byte)
    (bounded : (2 * index).toNat + 2 < 2^64)
    (valid : TrieNibbleRange state out (2 * index))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + 2 * index)))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + 1)))) :
    ∃ post, evaluateHOLFiniteState state keyToNibblesTailStep = (none,post) ∧
      TrieNibbleRange post out (2 * (index + 1)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.clock = state.clock := by
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have outEntered : entered.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "b" ≠ ofString "out" by decide] using outLocal
  have indexEntered : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "b" ≠ ofString "i" by decide] using indexLocal
  have byteEntered : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have rangeEntered : TrieNibbleRange entered out (2 * index) := valid.after_frame rfl rfl rfl
  obtain ⟨output,bodyRun,range,indexAfter,clock⟩ := evaluate_keyNibble_pair_advance_no_wrap entered
    (ofString "b") byte out index outEntered indexEntered byteEntered bounded rangeEntered firstDomain secondDomain
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.op .add [.var .local (ofString "key"),.var .local (ofString "i")])) =
      some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,evalListHOLExact,keyLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,loaded]
  let post := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "b",state.locals.lookup (ofString "b"))}
  refine ⟨post,?_,range.after_frame rfl rfl rfl,?_,clock⟩
  · rw [source_keyNibble_tail_step,evaluateHOLFiniteState_dec_total]
    simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
    have associated := evaluate_seq_assoc entered
      (.storeByte (keyNibbleOutputAddress 0) (.shift .lsr (.var .local (ofString "b")) (.const 4)))
      (.storeByte (keyNibbleOutputAddress 1) (.op .and [.var .local (ofString "b"),.const 15]))
      (memzeroAdvance 1)
    change evaluateHOLFiniteState entered (.seq (keyNibblePair (ofString "b")) (memzeroAdvance 1)) = _ at associated
    have bodySource := associated.symm.trans bodyRun
    simpa only [entered,memzeroAdvance,post] using congrArg
      (fun result : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
        (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (ofString "b",state.locals.lookup (ofString "b"))})) bodySource
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "b",state.locals.lookup (ofString "b"))).lookup (ofString "i") = _
    rw [saved_local_lookup_other]
    · exact indexAfter
    · decide

#print axioms evaluate_keyToNibbles_tail_range_no_wrap
end InitECandidate.Runtime
