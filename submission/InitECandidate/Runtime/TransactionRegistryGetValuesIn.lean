import InitECandidate.Runtime.HashGetCallValueProperty
import InitECandidate.Runtime.HashTableValuesIn
import InitECandidate.Runtime.JournalSavedValuesIn
import InitECandidate.Runtime.TransactionRegistryWorldFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A numeric or pointer table lookup preserves every watched table and saved
journal value, and exposes the actual declaration continuation. -/
theorem TransactionRegistryWorld.table_get_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : table ∈ tables) (watched targets : Set (BitVec 64))
    (entries : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 66 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_get") [tableArgument,keyArgument]) = (none,post) ∧
      state.clock ≤ post.clock + 2 ^ 66 ∧ post.clock ≤ state.clock ∧
      TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post ∧
      (∀ other ∈ watched, HashTableValuesIn other targets post) ∧
      JournalSavedValuesIn journal count.toNat watched targets post ∧ post.locals = state.locals ∧
      (∀ name continuation, evaluateHOLFiniteState state
        (.decCall name (.comb [.one,.one]) (ofString "htab_get") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word present),.val (.word value)]) post) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,logicalReady,_,_⟩ := valid.journalWorld.world.ready table member
  have ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state :=
    logicalReady.after_read _ state (widths table) table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have usedBefore := ready.live.arrays.usedBefore
  have orderBefore := ready.live.arrays.orderBefore
  have endBound := ready.live.arrays.endBound
  have capacityBound : capacity.toNat ≤ 33806089496 := by omega
  obtain ⟨present,value,post,boolean,run,cost,remaining,locals,memory,globals,code,domain,endian,_,declaration⟩ :=
    ready.live.arrays.get_value_property state (widths table) table keys stride capacity used values order orderPos items key bits
      (fun _ => True) (valid.journalWorld.supported table member) tableArgument keyArgument arguments keyAligned keyWords keyBytes
      (by intro slot inside occupied value cell; trivial) (by omega)
  exact ⟨present,value,post,boolean,run,by omega,remaining,valid.after_read memory globals code domain endian,
    (fun other belongs => (entries other belongs).after_read memory domain endian),
    saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact congrFun memory _),locals,declaration⟩

#print axioms TransactionRegistryWorld.table_get_values_in
end InitECandidate.Runtime
