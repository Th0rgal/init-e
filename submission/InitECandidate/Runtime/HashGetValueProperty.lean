import InitECandidate.Runtime.HashGetBodyWidths
import InitECandidate.Runtime.HashGetTailValueCell
import InitECandidate.Runtime.HashTableArraysFindOccupiedSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every present htab_get result satisfies any property held by all occupied
value cells. The actual supported-width lookup and its memory frame are included. -/
theorem evaluate_source_hashGet_supported_value_property {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (property : BitVec 64 → Prop)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (entries : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot ≠ some 0 →
      ∀ value : BitVec 64, state.memory (values + slot * 8) = .word value → property value)
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_get) =
        (some (.returned (.rStruct [.val (.word present),.val (.word value)])),post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ (present ≠ 0 → property value) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian,locals,postArrays,decl⟩ :=
    arrays.find_supported_occupied state keyLength table keys stride capacity used values order orderPos count key bits supported
      _ _ arguments keyAligned keyWords keyBytes budget
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have i : entered.locals.lookup (ofString "i") = some (.val (.word found)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨present,value,boolean,tail,cellMeaning⟩ := evaluate_hashGetTail_value_cell entered table found capacity values t i inside
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state keyLength table keys stride capacity used values order orderPos count bits 16 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell16)
    (by change ready.memaddrs _; rw [addresses]; exact arrays.header_domain state keyLength table keys stride capacity used values order orderPos count bits 40 (by decide))
    (by change ready.memory _ = _; rw [memory]; exact arrays.cell40)
    (by intro slot bound; change ready.memaddrs _; rw [addresses]; exact (arrays.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits).valueDomain slot bound)
  have returnedProperty : present ≠ 0 → property value := by
    intro nonzero
    obtain ⟨strict,cell⟩ := cellMeaning nonzero
    have different : found ≠ capacity := by
      intro same
      have equal := congrArg BitVec.toNat same
      omega
    have occupiedBefore : hashOccupancyRead state used found ≠ some 0 := by
      have readEq : hashOccupancyRead ready used found = hashOccupancyRead state used found := by
        unfold hashOccupancyRead panMemLoadByteHOL
        simp only [memory,endian]
        by_cases available : ready.memaddrs (panByteAlignHOL (used + found))
        · have before : state.memaddrs (panByteAlignHOL (used + found)) := by rw [← addresses]; exact available
          simp only [if_pos available,if_pos before]
        · have before : ¬state.memaddrs (panByteAlignHOL (used + found)) := by rw [← addresses]; exact available
          simp only [if_neg available,if_neg before]
      rw [← readEq]
      exact occupied different
    apply entries found strict occupiedBefore value
    change ready.memory (values + found * 8) = .word value at cell
    rw [memory] at cell
    exact cell
  rw [source_hashGet_body,decl]
  change ∃ present value post, _ ∧ (let output := evaluateHOLFiniteState entered hashGetTail; _) = _ ∧ _
  rw [tail]
  exact ⟨present,value,_,boolean,rfl,cost,remaining,memory,globals,postCode,addresses,endian,returnedProperty⟩

#print axioms evaluate_source_hashGet_supported_value_property
end InitECandidate.Runtime
