import InitECandidate.Runtime.RlpSlicesInitializationBound
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.RlpSlicesLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful completion of the actual slice loop returns its fixed slice
count, rather than a value depending on unchecked item lengths or stores. -/
theorem rlpSlices_loop_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64) (valid : RlpSlicesLoopWitness state pointer count)
    (budget : (count.toNat - valid.index.toNat) * 12 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesLoopAndReturn = (some (.returned value),post)) :
    ∃ array : ValueHOL 64, value = .rStruct [array,.val (.word count)] := by
  obtain ⟨result,loopPost,loopRun,_,_,_,done,noReturn⟩ := evaluate_rlpSlices_loop_bounded state pointer count valid budget
  rw [source_rlpSlices_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    obtain ⟨next,_⟩ := done rfl
    change evaluateHOLFiniteState loopPost (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")])) =
      (some (.returned value),post) at run
    rw [evaluateHOLFiniteState_return] at run
    cases arrayLocal : loopPost.locals.lookup (ofString "arr") with
    | none => simp [evalHOLExact,evalListHOLExact,arrayLocal] at run
    | some array =>
      simp [evalHOLExact,evalListHOLExact,arrayLocal,next.countLocal] at run
      split at run
      · have equal := (Prod.mk.inj run).1
        exact ⟨array,PanSemResultExact.returned.inj (Option.some.inj equal.symm)⟩
      · cases run

/-- Initialization scopes retain the exact count in every successful result. -/
theorem rlpSlices_initialized_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesInitialized = (some (.returned value),post)) :
    ∃ array : ValueHOL 64, value = .rStruct [array,.val (.word count)] := by
  let initial := setVarHOLFinite (ofString "off") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
  have atPointer : initial.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "p" by decide,show ofString "i" ≠ ofString "p" by decide] using pointerLocal
  have atCount : initial.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "count" by decide,show ofString "i" ≠ ofString "count" by decide] using countLocal
  have atOffset : initial.locals.lookup (ofString "off") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let valid : RlpSlicesLoopWitness initial pointer count :=
    ⟨0,0,atPointer,atCount,atOffset,atIndex,by simp,code⟩
  rw [source_rlpSlices_initialized] at run
  obtain ⟨middle,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0
    (.dec (ofString "off") .one (.const 0) rlpSlicesLoopAndReturn) (some (.returned value)) (by rfl) run
  obtain ⟨output,tailRun,_⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) middle
    (ofString "off") (.const 0) 0 rlpSlicesLoopAndReturn (some (.returned value)) (by rfl) bodyRun
  exact rlpSlices_loop_return_contract initial output pointer count valid
    (by change count.toNat * 12 ≤ state.clock; exact budget) value tailRun

#print axioms rlpSlices_initialized_return_contract

#print axioms rlpSlices_loop_return_contract
end InitECandidate.Runtime
