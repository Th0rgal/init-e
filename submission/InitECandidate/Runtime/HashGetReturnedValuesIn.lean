import InitECandidate.Runtime.HashGetTailValuesIn
import InitECandidate.Runtime.HtabDelFrame
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A returned value of the complete original get belongs to its witness
registry whenever present. The query can have any alignment or readability. -/
theorem hashGet_returned_values_in {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table key capacity used values : BitVec 64) (bits : Nat) (targets : Set (BitVec 64))
    (code : s.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (tableLocal : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : s.locals.lookup (ofString "key") = some (.val (.word key)))
    (domain16 : s.memaddrs (table + 16)) (cell16 : s.memory (table + 16) = .word capacity)
    (domain48 : s.memaddrs (table + 48)) (cell48 : s.memory (table + 48) = .word used)
    (domain40 : s.memaddrs (table + 40)) (cell40 : s.memory (table + 40) = .word values)
    (valueDomain : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → s.memaddrs (values + slot * 8))
    (entries : HashTableValuesIn table targets s) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_get) =
      (some (.returned v),post)) :
    ∃ present value : BitVec 64, v = .rStruct [.val (.word present),.val (.word value)] ∧
      (present = 0 ∨ present = 1) ∧ (present ≠ 0 → value ∈ targets) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
    (ofString "key",.val (.word key))
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] =
        some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "htab_find_slot")
      [.val (.word table),.val (.word key)] =
      some (sourceFunctionBody Guest.guestFn_htab_find_slot,callee,.one) := by
    rw [code]
    exact pan_two_word_lookup _ _ _ _ _ table key (by decide) originalRuntimeCode_hashFind_lookup
  rw [source_hashGet_body] at run
  obtain ⟨indexValue,bodyPost,output,bodyRun,_,tail,_⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "i") (ofString "htab_find_slot")
      .one .one _ _ (sourceFunctionBody Guest.guestFn_htab_find_slot) hashGetTail callee v args lookup run
  let entry := callEntryStateHOLFinite s callee
  have tableE : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨index,word,selected⟩ := htabFindSlot_returned_occupied entry bodyPost table capacity used bits power code
    tableE domain16 cell16 domain48 cell48 indexValue bodyRun
  subst indexValue
  have frame := htabFindSlot_memoryFrame entry code
  rw [bodyRun] at frame
  obtain ⟨memory,_⟩ := frame
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
  rw [bodyRun] at metadata
  let ready := setVarHOLFinite (ofString "i") (.val (.word index)) {bodyPost with locals := s.locals}
  have tableR : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal]
  have indexR : ready.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have memR : ready.memory = s.memory := memory
  have domR : ready.memaddrs = s.memaddrs := metadata.2.1
  have beR : ready.be = s.be := metadata.2.2.1
  have occupiedR : index = capacity ∨ (index.toNat < capacity.toNat ∧ hashOccupancyRead ready used index ≠ some 0) := by
    rcases selected with same | ⟨lt,occupied⟩
    · exact Or.inl same
    · exact Or.inr ⟨lt,by rw [hashOccupancyRead_after_read s ready used memR domR beR]; exact occupied⟩
  exact hashGetTail_returned_values_in ready output table index capacity used values targets tableR indexR occupiedR
    (by rw [domR]; exact domain16) (by rw [memR]; exact cell16)
    (by rw [domR]; exact domain40) (by rw [memR]; exact cell40) (by rw [memR]; exact cell48)
    (by intro slot lt; rw [domR]; exact valueDomain slot lt)
    (entries.after_read memR domR beR) v tail

#print axioms hashGet_returned_values_in
end InitECandidate.Runtime
