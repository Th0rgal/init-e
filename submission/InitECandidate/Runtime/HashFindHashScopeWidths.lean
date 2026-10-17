import InitECandidate.Runtime.HashFindHashScope32
import InitECandidate.Runtime.HashCallWidths
import InitECandidate.Runtime.HashFindEnvironmentWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindHashScope20 {F : Type} (table keys stride capacity used values order orderPos count key : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 20 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindHashScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ready.keyLocal,ready.lengthLocal]
  have words : ∀ offset ∈ ([0,8] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply ready.keyWords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    change offset < 20
    omega
  have bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 16 + extra)) := by
    intro extra member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa using ready.keyBytes 16 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 17 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 18 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 19 (by decide)
  obtain ⟨hash,hashed,clock,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hash20_declaration state _ _ key arguments ready.code (by omega) keyAligned words bytes
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have environment : HashFindEnvironment 20 keys stride key capacity used entered :=
    HashFindEnvironment.after_hash 20 keys stride key capacity used hash state entered ready memory code addresses endian
      (by simp only [entered,setVarHOLFinite,locals])
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨found,post,tail,inside,cost,remaining,tailMemory,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := evaluate_hashFindIndexScope20_from_count table keys stride capacity used values order orderPos count key hash
    bits power keyAligned entered environment
      (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays memory code addresses endian) h (by omega)
  unfold hashFindHashScope
  rw [decl]
  change ∃ found post, (let output := evaluateHOLFiniteState entered hashFindIndexScope; _) = _ ∧ _
  rw [tail]
  exact ⟨found,_,rfl,inside,by change state.clock ≤ post.clock + 2 * capacity.toNat + 1; omega,
    by change post.clock ≤ state.clock; omega,tailMemory.trans memory,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩


theorem evaluate_hashFindHashScope52 {F : Type} (table keys stride capacity used values order orderPos count key : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 52 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindHashScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word (52 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ready.keyLocal,ready.lengthLocal]
  have words : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply ready.keyWords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    change offset < 52
    omega
  have bytes : ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 48 + extra)) := by
    intro extra member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa using ready.keyBytes 48 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 49 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 50 (by decide)
    · simpa [BitVec.add_assoc] using ready.keyBytes 51 (by decide)
  obtain ⟨hash,hashed,clock,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hash52_declaration state _ _ key arguments ready.code (by omega) keyAligned words bytes
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have environment : HashFindEnvironment 52 keys stride key capacity used entered :=
    HashFindEnvironment.after_hash 52 keys stride key capacity used hash state entered ready memory code addresses endian
      (by simp only [entered,setVarHOLFinite,locals])
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨found,post,tail,inside,cost,remaining,tailMemory,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := evaluate_hashFindIndexScope52_from_count table keys stride capacity used values order orderPos count key hash
    bits power keyAligned entered environment
      (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays memory code addresses endian) h (by omega)
  unfold hashFindHashScope
  rw [decl]
  change ∃ found post, (let output := evaluateHOLFiniteState entered hashFindIndexScope; _) = _ ∧ _
  rw [tail]
  exact ⟨found,_,rfl,inside,by change state.clock ≤ post.clock + 2 * capacity.toNat + 1; omega,
    by change post.clock ≤ state.clock; omega,tailMemory.trans memory,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩


#print axioms evaluate_hashFindHashScope20
#print axioms evaluate_hashFindHashScope52
end InitECandidate.Runtime
