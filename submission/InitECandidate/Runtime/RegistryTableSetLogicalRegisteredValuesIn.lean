import InitECandidate.Runtime.RegistryTableSetRegisteredValuesIn
import InitECandidate.Runtime.PanFreshLocalStateFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Plain sets retain transaction and pointer invariants when the snapshot is
logical only; the executed call does not require a snapshot local binding. -/
theorem TransactionRegistryWorld.table_set_logical_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count table key value : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state) (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : table ∈ watched → value ∈ targets)
    (fresh : ofString "snap" ∉ freeVarIdsHOL (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]))
    (ticks : 2 ^ 74 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + 2 ^ 74 ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count output.2 ∧
        (∀ other ∈ watched, HashTableValuesIn other targets output.2) ∧ JournalSavedValuesIn journal count.toNat watched targets output.2) := by
  let shadow := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  have shadowValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count shadow := valid.after_read rfl rfl rfl rfl rfl
  have shadowSnap : shadow.locals.lookup (ofString "snap") = some (.val (.word snapshot)) := by
    simp [shadow,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have contract := shadowValid.table_set_registered_values_in shadow widths tables fieldPointer ts journal snapshot count table key value
    shadowSnap member tableArgument keyArgument valueArgument arguments aligned words bytes watched targets watchedSubset
    (fun other belongs => (registered other belongs).after_read rfl rfl rfl)
    (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) newRegistered ticks
  obtain ⟨resultSame,frame⟩ := evaluate_fresh_local_nonlocal_state state (ofString "snap") (.val (.word snapshot))
    (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) fresh
  have clockSame := congrArg (fun s : PanSemStateFiniteExact 64 F => s.clock) frame
  have memory := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memory) frame.symm
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 F => s.globals) frame.symm
  have code := congrArg (fun s : PanSemStateFiniteExact 64 F => s.code) frame.symm
  have domain := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memaddrs) frame.symm
  have endian := congrArg (fun s : PanSemStateFiniteExact 64 F => s.be) frame.symm
  refine ⟨?_,?_,?_,?_⟩
  · rw [← resultSame]
    exact contract.1
  · have cost := contract.2.1
    change state.clock ≤ _ + 2 ^ 74 at cost
    change (evaluateHOLFiniteState shadow _).2.clock = (evaluateHOLFiniteState state _).2.clock at clockSame
    rw [clockSame] at cost
    exact cost
  · have remaining := contract.2.2.1
    change _ ≤ state.clock at remaining
    change (evaluateHOLFiniteState shadow _).2.clock = (evaluateHOLFiniteState state _).2.clock at clockSame
    rw [clockSame] at remaining
    exact remaining
  · intro success
    have joint := contract.2.2.2 (resultSame.trans success)
    exact ⟨joint.1.after_read memory globals code domain endian,
      (fun other belongs => (joint.2.1 other belongs).after_read memory domain endian),
      joint.2.2.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact congrFun memory _)⟩

#print axioms TransactionRegistryWorld.table_set_logical_registered_values_in
end InitECandidate.Runtime
