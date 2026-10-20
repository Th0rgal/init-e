import InitECandidate.Runtime.PtKeyUFindCallGD
import InitECandidate.Runtime.HashTableArraysFindWidths
/-!
`htab_find_slot` on a relocated table of any supported width with a key of any alignment
(`HashTableArraysInvariant.findK`): the result is a slot index or the capacity, the table invariant is kept, and the
call is bounded by `(n + 2)` times the capacity plus two clocks.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.findK {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat ≤ 33806089496)
    (keyWords : ∀ offset : Nat, offset < n.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < n.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : (n.toNat + 2) * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      state.clock ≤ ready.clock + (n.toNat + 2) * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have facts := invariant.insertion_memory state n table keys stride capacity used values order orderPos count bits
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
  have header := invariant.header_domain state n table keys stride capacity used values order orderPos count bits
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashFindK_declaration state tableArgument keyArgument n table keys stride capacity used values order orderPos count key bits invariant.code invariant.power sup keyFit
      (header 16 (by decide)) invariant.cell16 (header 0 (by decide)) invariant.cell0
      (header 8 (by decide)) invariant.cell8 (header 32 (by decide)) invariant.cell32
      (header 48 (by decide)) invariant.cell48 arrayDomain keyWords keyBytes invariant readable
      (by rw [← invariant.agreement]; exact invariant.room) arguments budget
  exact ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,
    HashTableArraysInvariant.after_read state ready n table keys stride capacity used values order orderPos count bits invariant memory code addresses endian,decl⟩

#print axioms HashTableArraysInvariant.findK
end InitECandidate.Runtime
