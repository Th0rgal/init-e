import InitECandidate.Runtime.HashTableReadyGetSupported
import InitECandidate.Runtime.OriginalHashGetCode
import InitECandidate.Runtime.PanTwoWordResultLookup
import InitECandidate.Runtime.PanDecCallReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual pair-returning lookup enters any caller continuation with the shared
mixed-operation invariant and a bounded source-clock cost. -/
theorem HashTableReady.get_supported_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (name : MlS) (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      post.locals.lookup name = some (.rStruct [.val (.word present),.val (.word value)]) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ other, other ≠ name → post.locals.lookup other = state.locals.lookup other) ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall name (.comb [.one,.one]) (ofString "htab_get") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState post continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  obtain ⟨present,value,bodyPost,boolean,run,postReady,cost,remaining,memory,globals,code,domain,endian⟩ :=
    entryReady.get_supported entry keyLength table pointer keys stride capacity used values order orderPos items key bits supported t k keyAligned keyWords keyBytes
      (by change 2 * capacity.toNat + 2 ≤ state.clock - 1; omega)
  let post := setVarHOLFinite name (.rStruct [.val (.word present),.val (.word value)]) {bodyPost with locals := state.locals}
  have installed : state.code.lookup (ofString "htab_get") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_get,.comb [.one,.one]) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_hashGet_lookup
  have lookup := pan_two_word_result_lookup state.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_get) table key (.comb [.one,.one]) (by decide) installed
  refine ⟨present,value,post,boolean,
    postReady.after_read bodyPost post keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
    ?_,?_,?_,memory,globals,code,domain,endian,?_,?_⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · change state.clock ≤ bodyPost.clock + 2 * capacity.toNat + 3
    change state.clock - 1 ≤ bodyPost.clock + 2 * capacity.toNat + 2 at cost
    omega
  · change bodyPost.clock ≤ state.clock
    change bodyPost.clock ≤ state.clock - 1 at remaining
    omega
  · intro other different
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · intro continuation
    exact evaluate_decCall_return_caller_locals state bodyPost name (ofString "htab_get") (.comb [.one,.one]) (.comb [.one,.one])
      [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_get) continuation callee
      (.rStruct [.val (.word present),.val (.word value)]) arguments lookup (by omega) run remaining
      (by simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]) (by simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL])

#print axioms HashTableReady.get_supported_declaration
end InitECandidate.Runtime
