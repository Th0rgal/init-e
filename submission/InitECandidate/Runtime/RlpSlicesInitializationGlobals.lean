import InitECandidate.Runtime.RlpSlicesReturnGlobals
import InitECandidate.Runtime.RlpSlicesInitializationBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_initialized_return_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 ≤ state.clock)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (domain : ∀ slot : BitVec 64, slot.toNat < count.toNat →
      state.memaddrs (array + slot * 16#64) ∧ state.memaddrs (array + slot * 16#64 + 8#64))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesInitialized = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSlicePrefix post array count.toNat ∧ post.globals = state.globals := by
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
  have atArray : initial.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide] using arrayLocal
  let memoryValid : RlpSlicesMemoryWitness initial pointer count array :=
    ⟨valid,atArray,fits,domain,rlpSlicePrefix_empty initial array⟩
  rw [source_rlpSlices_initialized] at run
  obtain ⟨middle,bodyRun,restoredI⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0
    (.dec (ofString "off") .one (.const 0) rlpSlicesLoopAndReturn) (some (.returned value)) (by rfl) run
  obtain ⟨output,tailRun,restoredOff⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) middle
    (ofString "off") (.const 0) 0 rlpSlicesLoopAndReturn (some (.returned value)) (by rfl) bodyRun
  obtain ⟨shape,filled,globals⟩ := rlpSlices_loop_return_globals initial output pointer count array memoryValid
    (by change count.toNat * 12 ≤ state.clock; exact budget) value tailRun
  refine ⟨shape,?_⟩
  rw [restoredI,restoredOff]
  refine ⟨?_,globals⟩
  intro slot inside
  obtain ⟨p,n,entry⟩ := filled slot inside
  exact ⟨p,n,RlpSliceEntry.after_frame output _ _ _ _ _ entry rfl rfl rfl⟩

#print axioms rlpSlices_initialized_return_globals
end InitECandidate.Runtime
