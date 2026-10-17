import InitECandidate.Runtime.HashTableReadyAlloc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful allocator call retains every mixed-operation table fact. -/
theorem HashTableReady.alloc_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer size : BitVec 64) (argument : ExpHOL 64)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word size)])
    (clock : state.clock ≠ 0)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos count bits
        (allocationEnd pointer size) post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧ post.be = state.be ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd pointer size))) state).globals ∧
      (∀ name continuation, evaluateHOLFiniteState state (.decCall name .one (ofString "alloc") [argument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) post) continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))}))) := by
  obtain ⟨post,run,postReady,ticks,memory,locals,code,domain,shapes,endian⟩ :=
    ready.alloc_call state keyLength table keys stride capacity used values order orderPos count bits pointer size argument arguments clock request
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,_,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments ready.live.arrays.code clock ready.live.frontier.heap request
      (allocationEnd_within_heap pointer size ready.live.frontier.bounded request)
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at decl globals
  exact ⟨post,run,postReady,ticks,memory,locals,code,domain,shapes,endian,globals,decl⟩

#print axioms HashTableReady.alloc_declaration
end InitECandidate.Runtime
