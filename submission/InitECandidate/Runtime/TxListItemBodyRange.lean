import InitECandidate.Runtime.TxListItemBodyBound
import InitECandidate.Runtime.RlpItemBodyRange
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txListItem_body_returned_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) txListItemArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (inputBound : length.toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (budget : 12 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_list_item) = (some (.returned value),post)) :
    ∃ payloadPointer payload : BitVec 64,
      value = .rStruct [.val (.word payloadPointer),.val (.word payload)] ∧
      pointer.toNat ≤ payloadPointer.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_item") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  rw [source_txListItem_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,memory,globals,_,_,_,_,tail,restored⟩ := evaluate_decCall_returned_global_memory_clock_scope
    state post (ofString "it") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
    txListItemArguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item)
    txListItemContinuation callee value args lookup run
  obtain ⟨kind,payloadPointer,payload,consumed,shape,endsWithin,noWrapPayload,startsWithin⟩ :=
    rlpItem_body_return_range entry bodyPost pointer length parsed atPointer atLength code
      (by change 11 ≤ state.clock - 1; omega) noWrap inputBound bodyRun
  subst parsed
  let entered := setVarHOLFinite (ofString "it")
    (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) ready
  have atItem : entered.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have returned : value = .rStruct [.val (.word payloadPointer),.val (.word payload)] := by
    change evaluateHOLFiniteState entered txListItemContinuation = _ at tail
    have condition : @evalHOLExact 64 F _ entered.toExact (fun a => Classical.propDecidable (entered.memaddrs a))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1)) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .notEqual kind 1 then 1 else 0))) := by
      simp [evalHOLExact,atItem]
    rw [source_txListItem_continuation,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at tail
    by_cases mismatch : Compiler.Encoders.Asm.wordCmpHOL .notEqual kind 1 = true
    · rw [mismatch] at tail
      simp only [if_true,show (1 : BitVec 64) ≠ 0 by decide,if_false] at tail
      have terminal := evaluate_raise_terminal entered (ofString "TxErr") (.const 18)
      have noReturn := evaluate_raise_no_return entered (ofString "TxErr") (.const 18) value
      cases raised : evaluateHOLFiniteState entered (.raise (ofString "TxErr") (.const 18)) with
      | mk result middle =>
        rw [raised] at tail terminal noReturn
        cases result with
        | none => exact False.elim (terminal rfl)
        | some stopped => exact False.elim (noReturn (Prod.mk.inj tail).1)
    · have falseFlag : Compiler.Encoders.Asm.wordCmpHOL .notEqual kind 1 = false := Bool.eq_false_iff.mpr mismatch
      rw [falseFlag] at tail
      simp only [if_false,if_true,evaluateHOLFiniteState_skip] at tail
      have actual : evaluateHOLFiniteState entered
          (.return (.rstruct [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))])) =
          (some (.returned (.rStruct [.val (.word payloadPointer),.val (.word payload)])),emptyLocalsHOLFinite entered) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atItem,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      exact PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (tail.symm.trans actual)).1)
  exact ⟨payloadPointer,payload,returned,startsWithin,endsWithin,noWrapPayload⟩

#print axioms txListItem_body_returned_range
end InitECandidate.Runtime
