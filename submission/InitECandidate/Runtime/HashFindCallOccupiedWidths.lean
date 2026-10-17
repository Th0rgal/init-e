import InitECandidate.Runtime.HashFindBodyOccupiedWidths
import InitECandidate.Runtime.OriginalHashFindCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFind20_declaration_occupied {F : Type} (state : PanSemStateFiniteExact 64 F) (tableArgument keyArgument : ExpHOL 64)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (20 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
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
  obtain ⟨found,post,body,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_hashFind20_occupied entry table keys stride capacity used values order orderPos count key bits code power keyAligned
      t k domain16 cell16 domain0 cell0 domain8 cell8 domain32 cell32 domain48 cell48 arrayDomain keyWords keyBytes
      (HashTableArraysInvariant.after_read state entry _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) readable room
      (by change 2 * capacity.toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [code]; exact originalRuntimeCode_hashFind_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word found))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨found,{post with locals := state.locals},inside,occupied,?_,?_,memory,globals,postCode,addresses,endian,rfl,?_⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2
    change state.clock - 1 ≤ post.clock + 2 * capacity.toNat + 1 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_find_slot") .one .one
      [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_find_slot)
      continuation callee (.val (.word found)) arguments lookup (by omega) body remaining shapeOk shapeOk


theorem evaluate_hashFind52_declaration_occupied {F : Type} (state : PanSemStateFiniteExact 64 F) (tableArgument keyArgument : ExpHOL 64)
    (table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (52 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte : UInt8,
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + current) = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead ready used found ≠ some 0) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
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
  obtain ⟨found,post,body,inside,occupied,cost,remaining,memory,globals,postCode,addresses,endian⟩ :=
    evaluate_source_hashFind52_occupied entry table keys stride capacity used values order orderPos count key bits code power keyAligned
      t k domain16 cell16 domain0 cell0 domain8 cell8 domain32 cell32 domain48 cell48 arrayDomain keyWords keyBytes
      (HashTableArraysInvariant.after_read state entry _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) readable room
      (by change 2 * capacity.toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [code]; exact originalRuntimeCode_hashFind_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word found))) .one = true := by simp [shapeOfHOLExact,shapeEqHOL]
  refine ⟨found,{post with locals := state.locals},inside,occupied,?_,?_,memory,globals,postCode,addresses,endian,rfl,?_⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 2
    change state.clock - 1 ≤ post.clock + 2 * capacity.toNat + 1 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_find_slot") .one .one
      [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_find_slot)
      continuation callee (.val (.word found)) arguments lookup (by omega) body remaining shapeOk shapeOk


#print axioms evaluate_hashFind20_declaration_occupied
#print axioms evaluate_hashFind52_declaration_occupied
end InitECandidate.Runtime
