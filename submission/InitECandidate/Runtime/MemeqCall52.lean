import InitECandidate.Runtime.MemeqBodyWidths
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original aligned32 comparison declaration-call spends exactly one clock,
preserves memory, and binds its Boolean result in the actual continuation. -/
theorem evaluate_memeq52_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (aArgument bArgument sizeArgument : ExpHOL 64) (a b : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [aArgument,bArgument,sizeArgument] =
        some [.val (.word a),.val (.word b),.val (.word (52 : BitVec 64))])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0)
    (wordDomain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([48,49,50,51] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, ∃ ready, (value = 0 ∨ value = 1) ∧
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.locals = state.locals ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "memeq") [aArgument,bArgument,sizeArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "a",.val (.word a))).update
      (ofString "b",.val (.word b))).update (ofString "n",.val (.word (52 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have na : ofString "n" ≠ ofString "a" := by decide
  have nb : ofString "n" ≠ ofString "b" := by decide
  have ba : ofString "b" ≠ ofString "a" := by decide
  have aLocal : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,na,ba]
  have bLocal : entry.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,nb]
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word (52 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,post,boolean,body,ticks,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_memeq52 entry a b aLocal bLocal sizeLocal aAligned bAligned wordDomain byteDomain
  have installed : state.code.lookup (ofString "memeq") =
      some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
    rw [code]; exact originalRuntimeCode_memeq_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memeq) a b 52 (by decide) (by decide) (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word value))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨value,{post with locals := state.locals},boolean,ticks,memory,rfl,globals,postCode,addresses,endian,?_⟩
  intro name continuation
  exact evaluate_decCall_return_caller_locals state post name (ofString "memeq") .one .one
    [aArgument,bArgument,sizeArgument] [.val (.word a),.val (.word b),.val (.word (52 : BitVec 64))]
    (sourceFunctionBody Guest.guestFn_memeq) continuation callee (.val (.word value))
    arguments lookup clock body (Nat.le_of_eq ticks) shapeOk shapeOk

#print axioms evaluate_memeq52_declaration
end InitECandidate.Runtime
