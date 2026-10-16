import InitECandidate.Runtime.HashBody32
import InitECandidate.Runtime.OriginalHashCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original aligned32 hash declaration-call: one entry clock, no
memory effects, and caller locals restored around its result binding. -/
theorem evaluate_hash32_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointerArgument lengthArgument : ExpHOL 64) (pointer : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [pointerArgument,lengthArgument] =
        some [.val (.word pointer),.val (.word (32 : BitVec 64))])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : pointer.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset)) :
    ∃ value : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.locals = state.locals ∧ ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_hash") [pointerArgument,lengthArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "key_len",.val (.word (32 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key_len" ≠ ofString "p" := by decide
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have n : entry.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,body,ticks,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_hash32 entry pointer p n aligned domain
  have installed : state.code.lookup (ofString "htab_hash") =
      some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
    rw [code]; exact originalRuntimeCode_hash_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
    (sourceFunctionBody Guest.guestFn_htab_hash) pointer 32 (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word value))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨value,{post with locals := state.locals},ticks,memory,globals,postCode,addresses,endian,rfl,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "htab_hash") .one .one
    [pointerArgument,lengthArgument] [.val (.word pointer),.val (.word (32 : BitVec 64))]
    (sourceFunctionBody Guest.guestFn_htab_hash) continuation callee (.val (.word value))
    arguments lookup clock body (Nat.le_of_eq ticks) shapeOk shapeOk

#print axioms evaluate_hash32_declaration
end InitECandidate.Runtime
