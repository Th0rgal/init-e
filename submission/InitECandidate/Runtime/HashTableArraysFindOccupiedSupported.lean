import InitECandidate.Runtime.HashTableArraysFindOccupiedWidths
import InitECandidate.Runtime.HashTableArraysFindOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.find_supported_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  rcases supported with rfl | rfl | rfl
  · exact invariant.find20_occupied state table keys stride capacity used values order orderPos count key bits
      tableArgument keyArgument arguments keyAligned keyWords keyBytes budget
  · have old := (hashTableArraysInvariant_32_iff table keys stride capacity used values order orderPos count bits state).mp invariant
    have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
      intro offset member
      apply keyWords
      change offset < 32
      simp at member
      omega
    obtain ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,domain,endian,locals,arrays,decl⟩ :=
      old.find_occupied state table keys stride capacity used values order orderPos count key bits
        tableArgument keyArgument arguments keyAligned keyDomain budget
    exact ⟨found,ready,inside,occupied,cost,remaining,memory,globals,code,domain,endian,locals,
      (hashTableArraysInvariant_32_iff table keys stride capacity used values order orderPos count bits ready).mpr arrays,decl⟩
  · exact invariant.find52_occupied state table keys stride capacity used values order orderPos count key bits
      tableArgument keyArgument arguments keyAligned keyWords keyBytes budget

#print axioms HashTableArraysInvariant.find_supported_occupied
end InitECandidate.Runtime
