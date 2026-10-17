import InitECandidate.Runtime.TransactionRegistryGetValuesIn
import InitECandidate.Runtime.TransactionAccountReadRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateAccountCachedScope (fallback : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "w") (.comb [.one,.one]) (ofString "htab_get")
    [.load .one (.op .add [.var .global (ofString "ts"),.const 16]),.var .local (ofString "addr")]
    (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
      (.return (.rfield 1 (.var .local (ofString "w")))) .skip) fallback)

def stateAccountPreStateFallback : ProgHOL 64 :=
  .decCall (ofString "a") .one (ofString "get_pre_state_account_optional") [.var .local (ofString "addr")]
    (.return (.var .local (ofString "a")))

theorem source_getAccountOptional_cached_scope :
    sourceFunctionBody Guest.guestFn_get_account_optional =
      .seq stateAccountReadTrack (stateAccountCachedScope stateAccountPreStateFallback) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual cached-account lookup retains the transaction and pointer
invariants and selects precisely the cached return or pre-state continuation. -/
theorem TransactionRegistryWorld.account_cached_lookup {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count table addr : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (binding : (16,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (aligned : addr.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64))
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (ticks : 2 ^ 66 ≤ state.clock) :
    ∃ present account : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      state.clock ≤ post.clock + 2 ^ 66 ∧ post.clock ≤ state.clock ∧
      TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post ∧
      (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal count.toNat watched targets post ∧
      post.locals = state.locals ∧
      (∀ fallback, evaluateHOLFiniteState state (stateAccountCachedScope fallback) =
        (let entered := setVarHOLFinite (ofString "w") (.rStruct [.val (.word present),.val (.word account)]) post;
         let output := if present = 0 then evaluateHOLFiniteState entered fallback
           else (some (.returned (.val (.word account))),emptyLocalsHOLFinite entered);
         (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "w",state.locals.lookup (ofString "w"))}))) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const 16])) = some (.val (.word table)) :=
    (valid.load_registered state widths tables fieldPointer ts journal snapshot count 16 table binding).1
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.load .one (.op .add [.var .global (ofString "ts"),.const 16]),.var .local (ofString "addr")] =
      some [.val (.word table),.val (.word addr)] := by
    simp only [evalListHOLFinite,evalListHOLExact]
    rw [loaded]
    simp [evalHOLExact,addrLocal]
  obtain ⟨present,account,post,boolean,_,cost,remaining,postWorld,postValues,postSaved,locals,declaration⟩ :=
    valid.table_get_values_in state widths tables fieldPointer ts journal snapshot count table addr
      (valid.load_registered state widths tables fieldPointer ts journal snapshot count 16 table binding).2
      watched targets registered saved _ _ args aligned words bytes ticks
  refine ⟨present,account,post,boolean,cost,remaining,postWorld,postValues,postSaved,locals,?_⟩
  intro fallback
  let entered := setVarHOLFinite (ofString "w") (.rStruct [.val (.word present),.val (.word account)]) post
  have w : entered.locals.lookup (ofString "w") = some (.rStruct [.val (.word present),.val (.word account)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  unfold stateAccountCachedScope
  rw [declaration]
  dsimp only
  by_cases absent : present = 0
  · have condition : @evalHOLExact 64 F _ entered.toExact
        (fun address => Classical.propDecidable (entered.memaddrs address))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,w,Compiler.Encoders.Asm.wordCmpHOL,absent]
    rw [if_pos absent]
    change (let output := evaluateHOLFiniteState entered (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) (.return (.rfield 1 (.var .local (ofString "w")))) .skip) fallback); _) = _
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [evaluateHOLFiniteState_skip,if_true]
    rfl
  · have condition : @evalHOLExact 64 F _ entered.toExact
        (fun address => Classical.propDecidable (entered.memaddrs address))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,w,Compiler.Encoders.Asm.wordCmpHOL]
      exact absent
    have returned : evaluateHOLFiniteState entered (.return (.rfield 1 (.var .local (ofString "w")))) =
        (some (.returned (.val (.word account))),emptyLocalsHOLFinite entered) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,w,shapeOfHOLExact]
    rw [if_neg absent]
    change (let output := evaluateHOLFiniteState entered (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) (.return (.rfield 1 (.var .local (ofString "w")))) .skip) fallback); _) = _
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    change (let output := evaluateHOLFiniteState entered (.return (.rfield 1 (.var .local (ofString "w")))); _) = _
    rw [returned]
    rfl

#print axioms source_getAccountOptional_cached_scope
#print axioms TransactionRegistryWorld.account_cached_lookup
end InitECandidate.Runtime
