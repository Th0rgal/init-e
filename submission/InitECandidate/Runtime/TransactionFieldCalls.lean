import InitECandidate.Runtime.TransactionRuntimeWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual jset call whose table argument is loaded from the transaction
header retains the complete invariant, with membership proved from that field. -/
theorem TransactionRuntimeWorld.jset_field_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count table key value : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (offset : Nat)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (keyArgument valueArgument : ExpHOL 64)
    (keyEval : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      keyArgument = some (.val (.word key)))
    (valueEval : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      valueArgument = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [(.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])),keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 73 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRuntimeWorld widths fieldPointer ts journal snapshot (count + 1) output.2) := by
  have loaded := valid.load_registered state widths fieldPointer ts journal snapshot count offset table binding
  apply valid.jset_call state widths fieldPointer ts journal snapshot count table key value loaded.2
    (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) keyArgument valueArgument ?_ keyAligned keyWords keyBytes ticks
  simp only [evalListHOLFinite,evalListHOLExact,loaded.1,keyEval,valueEval]

#print axioms TransactionRuntimeWorld.jset_field_call

/-- An actual jdel call whose table argument is loaded from the transaction
header retains the complete invariant, with membership proved from that field. -/
theorem TransactionRuntimeWorld.jdel_field_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count state)
    (offset : Nat)
    (binding : (offset,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (keyArgument : ExpHOL 64)
    (keyEval : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      keyArgument = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [(.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])),keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧ TransactionRuntimeWorld widths fieldPointer ts journal snapshot next output.2) := by
  have loaded := valid.load_registered state widths fieldPointer ts journal snapshot count offset table binding
  apply valid.jdel_call state widths fieldPointer ts journal snapshot count table key loaded.2
    (.load .one (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 offset)])) keyArgument ?_ keyAligned keyWords keyBytes ticks
  simp only [evalListHOLFinite,evalListHOLExact,loaded.1,keyEval]

#print axioms TransactionRuntimeWorld.jdel_field_call

end InitECandidate.Runtime
