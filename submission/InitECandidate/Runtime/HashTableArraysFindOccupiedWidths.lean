import InitECandidate.Runtime.HashTableArraysMemory
import InitECandidate.Runtime.HashFindCallOccupiedWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.find20_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have facts := invariant.insertion_memory state 20 table keys stride capacity used values order orderPos count bits
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
  have header := invariant.header_domain state 20 table keys stride capacity used values order orderPos count bits
  obtain ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashFind20_declaration_occupied state tableArgument keyArgument table keys stride capacity used values order orderPos count key bits invariant.code invariant.power keyAligned
      (header 16 (by decide)) invariant.cell16 (header 0 (by decide)) invariant.cell0
      (header 8 (by decide)) invariant.cell8 (header 32 (by decide)) invariant.cell32
      (header 48 (by decide)) invariant.cell48 arrayDomain keyWords keyBytes invariant readable
      (by rw [← invariant.agreement]; exact invariant.room) arguments budget
  exact ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,
    HashTableArraysInvariant.after_read state ready 20 table keys stride capacity used values order orderPos count bits invariant memory code addresses endian,decl⟩


theorem HashTableArraysInvariant.find52_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have facts := invariant.insertion_memory state 52 table keys stride capacity used values order orderPos count bits
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
  have header := invariant.header_domain state 52 table keys stride capacity used values order orderPos count bits
  obtain ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashFind52_declaration_occupied state tableArgument keyArgument table keys stride capacity used values order orderPos count key bits invariant.code invariant.power keyAligned
      (header 16 (by decide)) invariant.cell16 (header 0 (by decide)) invariant.cell0
      (header 8 (by decide)) invariant.cell8 (header 32 (by decide)) invariant.cell32
      (header 48 (by decide)) invariant.cell48 arrayDomain keyWords keyBytes invariant readable
      (by rw [← invariant.agreement]; exact invariant.room) arguments budget
  exact ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,addresses,endian,locals,
    HashTableArraysInvariant.after_read state ready 52 table keys stride capacity used values order orderPos count bits invariant memory code addresses endian,decl⟩


#print axioms HashTableArraysInvariant.find20_occupied
#print axioms HashTableArraysInvariant.find52_occupied
end InitECandidate.Runtime
