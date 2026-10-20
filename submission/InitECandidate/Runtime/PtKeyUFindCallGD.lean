import InitECandidate.Runtime.PtKeyUFindBodyGD
import InitECandidate.Runtime.HashFindCallWidths
/-!
The actual `htab_find_slot` declaration-call for 20/32/52-byte keys at any key alignment, bounded by `(n + 2)` times
the capacity plus two.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindK_declaration {F : Type} (state : PanSemStateFiniteExact 64 F) (tableArgument keyArgument : ExpHOL 64)
    (n table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat ≤ 33806089496)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word n)
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyWords : ∀ offset : Nat, offset < n.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < n.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (budget : (n.toNat + 2) * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      state.clock ≤ ready.clock + (n.toNat + 2) * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨found,post,body,inside,cost,remaining,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_hashFindK entry n table keys stride capacity used values order orderPos count key bits code power sup keyFit
      t k domain16 cell16 domain0 cell0 domain8 cell8 domain32 cell32 domain48 cell48 arrayDomain keyWords keyBytes
      (HashTableArraysInvariant.after_read state entry _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) readable room
      (by change (n.toNat + 2) * capacity.toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [code]; exact originalRuntimeCode_hashFind_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word found))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨found,{post with locals := state.locals},inside,?_,?_,memory,globals,postCode,addresses,endian,rfl,?_⟩
  · change state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat + 2
    change state.clock - 1 ≤ post.clock + (n.toNat + 2) * capacity.toNat + 1 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_find_slot") .one .one
      [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_find_slot)
      continuation callee (.val (.word found)) arguments lookup (by omega) body remaining shapeOk shapeOk

#print axioms evaluate_hashFindK_declaration
end InitECandidate.Runtime
