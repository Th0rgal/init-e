import InitECandidate.Runtime.TransactionAllocationSuffixBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original decoder suffix exposes the exact state after allocating
its400-byte transaction record; the allocator changes only heap_ptr and clock. -/
theorem transaction_allocation_returned_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (run : evaluateHOLFiniteState state (transactionAt 2) = (some (.returned value),post)) :
    ∃ entry output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState entry (transactionAt 3) = (some (.returned value),output) ∧
      entry.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (∀ name, name ≠ ofString "tx" → entry.locals.lookup name = state.locals.lookup name) ∧
      entry.memory = state.memory ∧ entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧
      entry.clock = state.clock - 1 ∧
      entry.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd tx 400))) state).globals ∧
      (post.memory = output.memory ∧ post.globals = output.globals) := by
  have endNat : (allocationEnd tx 400).toNat = tx.toNat + 400 :=
    allocationEnd_aligned_toNat tx 400 small aligned (by decide)
  obtain ⟨ready,_,ticks,memory,locals,postCode,domain,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 400) tx 400 (by rfl) code clock heap
      (allocationGuard_of_sum_bound tx 400 small) (by rw [endNat]; exact small)
  let entry := setVarHOLFinite (ofString "tx") (.val (.word tx)) ready
  have atTx : entry.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have localFrame : ∀ name, name ≠ ofString "tx" → entry.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  rw [source_transaction_allocation,declaration] at run
  cases bodyRun : evaluateHOLFiniteState entry (transactionAt 3) with
  | mk result output =>
    change (let body := evaluateHOLFiniteState entry (transactionAt 3); _) = _ at run
    rw [bodyRun] at run
    have returned := (Prod.mk.inj run).1
    change result = some (.returned value) at returned
    subst result
    refine ⟨entry,output,bodyRun,atTx,localFrame,memory,postCode,domain,ticks,globals,?_⟩
    have restored := (Prod.mk.inj run).2
    exact ⟨(congrArg PanSemStateFiniteExact.memory restored).symm,
      (congrArg PanSemStateFiniteExact.globals restored).symm⟩

#print axioms transaction_allocation_returned_state
end InitECandidate.Runtime
