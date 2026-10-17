import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashFindCallOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem HashTableArraysInvariant32.find_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos count bits
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have limit := invariant.endBound
  have arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address := by
    intro address lower upper
    apply invariant.domain <;> omega
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte := by
    intro current inside
    have available := facts.byteDomain current inside
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  have header := invariant.header_domain state table keys stride capacity used values order orderPos count bits
  obtain ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashFind32_declaration_occupied state tableArgument keyArgument table keys stride key capacity used bits invariant.code invariant.power
      invariant.keysAligned invariant.strideAligned keyAligned invariant.fits (by omega)
      (header 16 (by decide)) invariant.cell16 (header 0 (by decide)) invariant.cell0
      (header 8 (by decide)) invariant.cell8 (header 32 (by decide)) invariant.cell32
      (header 48 (by decide)) invariant.cell48 arrayDomain keyDomain readable
      (by rw [← invariant.agreement]; exact invariant.room) arguments budget
  exact ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,
    invariant.after_read state ready table keys stride capacity used values order orderPos count bits memory code addresses endian,decl⟩

#print axioms HashTableArraysInvariant32.find_occupied
end InitECandidate.Runtime
