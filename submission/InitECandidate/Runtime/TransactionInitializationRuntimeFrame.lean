import InitECandidate.Runtime.TransactionInitializationLowerFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Record initialization consumes at most401 ticks and preserves the caller's
local/global environment and memory domain, even on a header-store error. -/
theorem transaction_record_initialization_runtime_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (code : state.code = originalRuntimeCode) (budget : 401 ≤ state.clock)
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address) :
    let output := evaluateHOLFiniteState state transactionRecordInitialization
    state.clock ≤ output.2.clock + 401 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut ∧
      output.2.locals = state.locals ∧ output.2.globals = state.globals ∧ output.2.code = state.code ∧
      output.2.memaddrs = state.memaddrs := by
  obtain ⟨words,bytes⟩ := memzero_interval_domains state tx 400 aligned (by change tx.toNat + 400 ≤ 2^64; omega) arena
  obtain ⟨middle,run,_,cost,remaining,globals,postCode,domain,_,locals,_⟩ := evaluate_memzero_aligned_call state
    (.var .local (ofString "tx")) (.const 400) tx 400
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,txLocal]) code budget small aligned words bytes
  let headers : ProgHOL 64 := .seq transactionInputPointerStore transactionInputLengthStore
  have clock := clockPreserving_of_straightLine headers (by rfl) middle
  have safe := evaluate_straightLine_no_timeout headers (by rfl) middle
  have headerLocals : (evaluateHOLFiniteState middle headers).2.locals = middle.locals := by
    apply HolFiniteMapExact.ext
    funext key
    exact evaluate_straight_local_frame key headers (by rfl) middle
  have headerGlobals : (evaluateHOLFiniteState middle headers).2.globals = middle.globals := by
    apply HolFiniteMapExact.ext
    funext key
    exact evaluate_avoidsGlobalAssignment key headers (by rfl) middle
  have metadata := evaluateHOLFiniteState_metadata middle headers
  rw [transactionRecordInitialization,evaluateHOLFiniteState_seq_line780,run]
  dsimp only
  change state.clock ≤ (evaluateHOLFiniteState middle headers).2.clock + 401 ∧ _
  refine ⟨?_,?_,safe,headerLocals.trans locals,headerGlobals.trans globals,metadata.1.trans postCode,metadata.2.1.trans domain⟩
  · change state.clock ≤ middle.clock + 400 + 1 at cost
    omega
  · change (evaluateHOLFiniteState middle headers).2.clock ≤ state.clock
    rw [clock]
    exact remaining

#print axioms transaction_record_initialization_runtime_frame
end InitECandidate.Runtime
