import InitECandidate.Runtime.HashTableValuesInInsertCall
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesWidthKU
import InitECandidate.Runtime.HashInsertProbeEntriesWidthKU
import InitECandidate.Runtime.HashInsertIndexEntriesWidthKU
import InitECandidate.Runtime.HashInsertHashAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertBodyAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
import InitECandidate.Runtime.HashInsertIndexLinkedWidthKU
import InitECandidate.Runtime.HashInsertHashLinkedSupportedKU
import InitECandidate.Runtime.HashInsertBodyLinkedSupportedKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCallLinkedSupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
import InitECandidate.Runtime.HashTableArraysFrameSupportedKU
import InitECandidate.Runtime.HashTableArraysAllEntriesSupportedKU
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertSupportedKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
/-! Unaligned-key copy of `HashTableValuesInInsertCall` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
set_option linter.unusedSimpArgs false
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual supported-width insertion preserves registered-pointer
membership through hashing, probing, copy, stores, and caller scope restoration. -/
theorem evaluate_hashInsert_hash_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count keys stride key keyLength : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (budget : capacity.toNat + keyLength.toNat + 2 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashInsertHashScope =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2 ∧ post.clock ≤ state.clock ∧
      HashTableValuesIn table targets post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word keyLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,keyLocal,lengthLocal]
  obtain ⟨hash,hashed,clock,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hash_supported_declarationKU state _ _ key keyLength arguments invariant.code (by omega)
      sourceAligned len8 keyFit supported sourceWordDomain sourceByteDomain
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInvariant := invariant.after_read state entered keyLength table keys stride capacity used values order orderPos count bits
    memory postCode addresses endian
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨post,tail,header,agreement,cost,remaining,preserved,postGlobals,code,domain,postEndian⟩ :=
    evaluate_hashInsert_index_values_inKU entered capacity used table values value order orderPos count hash keys stride key keyLength bits
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans orderLocal)
      ((other _ (by decide)).trans orderPosLocal) ((other _ (by decide)).trans valueLocal)
      h ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      (by omega) enteredInvariant sourceAligned len8 keyFit
      (by change ∀ offset : Nat, _ → hashed.memaddrs _; rw [addresses]; exact sourceWordDomain)
      (by change ∀ offset : Nat, _ → hashed.memaddrs _; rw [addresses]; exact sourceByteDomain)
      keysBeforeValues
      targets (entries.after_read memory addresses endian) member
  unfold hashInsertHashScope
  rw [decl]
  change ∃ post, (let output := evaluateHOLFiniteState entered hashInsertIndexScope; _) = _ ∧ _
  rw [tail]
  refine ⟨_,rfl,header,agreement,?_,?_,?_,postGlobals.trans globals,code.trans postCode,domain.trans addresses,postEndian.trans endian⟩
  · change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2; omega
  · change post.clock ≤ state.clock; omega
  · exact preserved.after_read rfl rfl rfl


/-- The actual supported-width insertion preserves registered-pointer
membership through hashing, probing, copy, stores, and caller scope restoration. -/
theorem evaluate_source_hashInsert_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count keys stride key keyLength : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (budget : capacity.toNat + keyLength.toNat + 2 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 2 ∧ post.clock ≤ state.clock ∧
      HashTableValuesIn table targets post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have headerDomain := invariant.header_domain state keyLength table keys stride capacity used values order orderPos count bits
  have domain16 := headerDomain 16 (by decide)
  have cell16 := invariant.cell16
  have domain0 := headerDomain 0 (by decide)
  have cell0 := invariant.cell0
  have domain8 := headerDomain 8 (by decide)
  have cell8 := invariant.cell8
  have domain32 := headerDomain 32 (by decide)
  have cell32 := invariant.cell32
  have domain48 := headerDomain 48 (by decide)
  have cell48 := invariant.cell48
  have domain56 := headerDomain 56 (by decide)
  have cell56 := invariant.cell56
  have domain64 := headerDomain 64 (by decide)
  have cell64 := invariant.cell64
  have n0_1 : ofString "cap" ≠ ofString "klen" := by decide
  have n0_2 : ofString "cap" ≠ ofString "stride" := by decide
  have n0_3 : ofString "cap" ≠ ofString "keys" := by decide
  have n0_4 : ofString "cap" ≠ ofString "used" := by decide
  have n0_5 : ofString "cap" ≠ ofString "order" := by decide
  have n0_6 : ofString "cap" ≠ ofString "order_pos" := by decide
  have n0_7 : ofString "cap" ≠ ofString "t" := by decide
  have n0_8 : ofString "cap" ≠ ofString "key" := by decide
  have n0_9 : ofString "cap" ≠ ofString "value" := by decide
  have n1_2 : ofString "klen" ≠ ofString "stride" := by decide
  have n1_3 : ofString "klen" ≠ ofString "keys" := by decide
  have n1_4 : ofString "klen" ≠ ofString "used" := by decide
  have n1_5 : ofString "klen" ≠ ofString "order" := by decide
  have n1_6 : ofString "klen" ≠ ofString "order_pos" := by decide
  have n1_7 : ofString "klen" ≠ ofString "t" := by decide
  have n1_8 : ofString "klen" ≠ ofString "key" := by decide
  have n1_9 : ofString "klen" ≠ ofString "value" := by decide
  have n2_3 : ofString "stride" ≠ ofString "keys" := by decide
  have n2_4 : ofString "stride" ≠ ofString "used" := by decide
  have n2_5 : ofString "stride" ≠ ofString "order" := by decide
  have n2_6 : ofString "stride" ≠ ofString "order_pos" := by decide
  have n2_7 : ofString "stride" ≠ ofString "t" := by decide
  have n2_8 : ofString "stride" ≠ ofString "key" := by decide
  have n2_9 : ofString "stride" ≠ ofString "value" := by decide
  have n3_4 : ofString "keys" ≠ ofString "used" := by decide
  have n3_5 : ofString "keys" ≠ ofString "order" := by decide
  have n3_6 : ofString "keys" ≠ ofString "order_pos" := by decide
  have n3_7 : ofString "keys" ≠ ofString "t" := by decide
  have n3_8 : ofString "keys" ≠ ofString "key" := by decide
  have n3_9 : ofString "keys" ≠ ofString "value" := by decide
  have n4_5 : ofString "used" ≠ ofString "order" := by decide
  have n4_6 : ofString "used" ≠ ofString "order_pos" := by decide
  have n4_7 : ofString "used" ≠ ofString "t" := by decide
  have n4_8 : ofString "used" ≠ ofString "key" := by decide
  have n4_9 : ofString "used" ≠ ofString "value" := by decide
  have n5_6 : ofString "order" ≠ ofString "order_pos" := by decide
  have n5_7 : ofString "order" ≠ ofString "t" := by decide
  have n5_8 : ofString "order" ≠ ofString "key" := by decide
  have n5_9 : ofString "order" ≠ ofString "value" := by decide
  have n6_7 : ofString "order_pos" ≠ ofString "t" := by decide
  have n6_8 : ofString "order_pos" ≠ ofString "key" := by decide
  have n6_9 : ofString "order_pos" ≠ ofString "value" := by decide
  let s1 := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run1 : ∀ continuation, evaluateHOLFiniteState state
      (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16)) continuation) =
      (let output := evaluateHOLFiniteState s1 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "cap",state.locals.lookup (ofString "cap")))})) := by
    intro continuation
    exact evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity continuation t1 domain16 cell16
  let s2 := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run2 : ∀ continuation, evaluateHOLFiniteState s1
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0)) continuation) =
      (let output := evaluateHOLFiniteState s2 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "klen",s1.locals.lookup (ofString "klen")))})) := by
    intro continuation
    exact evaluate_header_load_scope s1 (ofString "klen") (ofString "t") table 0 keyLength continuation t2 domain0 cell0
  let s3 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run3 : ∀ continuation, evaluateHOLFiniteState s2
      (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8)) continuation) =
      (let output := evaluateHOLFiniteState s3 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "stride",s2.locals.lookup (ofString "stride")))})) := by
    intro continuation
    exact evaluate_header_load_scope s2 (ofString "stride") (ofString "t") table 8 stride continuation t3 domain8 cell8
  let s4 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run4 : ∀ continuation, evaluateHOLFiniteState s3
      (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32)) continuation) =
      (let output := evaluateHOLFiniteState s4 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "keys",s3.locals.lookup (ofString "keys")))})) := by
    intro continuation
    exact evaluate_header_load_scope s3 (ofString "keys") (ofString "t") table 32 keys continuation t4 domain32 cell32
  let s5 := setVarHOLFinite (ofString "used") (.val (.word used)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run5 : ∀ continuation, evaluateHOLFiniteState s4
      (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48)) continuation) =
      (let output := evaluateHOLFiniteState s5 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "used",s4.locals.lookup (ofString "used")))})) := by
    intro continuation
    exact evaluate_header_load_scope s4 (ofString "used") (ofString "t") table 48 used continuation t5 domain48 cell48
  let s6 := setVarHOLFinite (ofString "order") (.val (.word order)) s5
  have t6 : s5.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run6 : ∀ continuation, evaluateHOLFiniteState s5
      (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56)) continuation) =
      (let output := evaluateHOLFiniteState s6 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "order",s5.locals.lookup (ofString "order")))})) := by
    intro continuation
    exact evaluate_header_load_scope s5 (ofString "order") (ofString "t") table 56 order continuation t6 domain56 cell56
  let s7 := setVarHOLFinite (ofString "order_pos") (.val (.word orderPos)) s6
  have t7 : s6.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have run7 : ∀ continuation, evaluateHOLFiniteState s6
      (.dec (ofString "order_pos") .one (.load .one (hashLocalAddress (ofString "t") 64)) continuation) =
      (let output := evaluateHOLFiniteState s7 continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (ofString "order_pos",s6.locals.lookup (ofString "order_pos")))})) := by
    intro continuation
    exact evaluate_header_load_scope s6 (ofString "order_pos") (ofString "t") table 64 orderPos continuation t7 domain64 cell64
  have capBinding : s7.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have klenBinding : s7.locals.lookup (ofString "klen") = some (.val (.word keyLength)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have strideBinding : s7.locals.lookup (ofString "stride") = some (.val (.word stride)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have keysBinding : s7.locals.lookup (ofString "keys") = some (.val (.word keys)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have usedBinding : s7.locals.lookup (ofString "used") = some (.val (.word used)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have orderBinding : s7.locals.lookup (ofString "order") = some (.val (.word order)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have orderPosBinding : s7.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)) := by
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9]
  have tableBinding : s7.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using tableLocal
  have keyBinding : s7.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using keyLocal
  have valueBinding : s7.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simpa [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,n0_1,n0_2,n0_3,n0_4,n0_5,n0_6,n0_7,n0_8,n0_9,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_9,n2_3,n2_4,n2_5,n2_6,n2_7,n2_8,n2_9,n3_4,n3_5,n3_6,n3_7,n3_8,n3_9,n4_5,n4_6,n4_7,n4_8,n4_9,n5_6,n5_7,n5_8,n5_9,n6_7,n6_8,n6_9,Ne.symm n0_1,Ne.symm n0_2,Ne.symm n0_3,Ne.symm n0_4,Ne.symm n0_5,Ne.symm n0_6,Ne.symm n0_7,Ne.symm n0_8,Ne.symm n0_9,Ne.symm n1_2,Ne.symm n1_3,Ne.symm n1_4,Ne.symm n1_5,Ne.symm n1_6,Ne.symm n1_7,Ne.symm n1_8,Ne.symm n1_9,Ne.symm n2_3,Ne.symm n2_4,Ne.symm n2_5,Ne.symm n2_6,Ne.symm n2_7,Ne.symm n2_8,Ne.symm n2_9,Ne.symm n3_4,Ne.symm n3_5,Ne.symm n3_6,Ne.symm n3_7,Ne.symm n3_8,Ne.symm n3_9,Ne.symm n4_5,Ne.symm n4_6,Ne.symm n4_7,Ne.symm n4_8,Ne.symm n4_9,Ne.symm n5_6,Ne.symm n5_7,Ne.symm n5_8,Ne.symm n5_9,Ne.symm n6_7,Ne.symm n6_8,Ne.symm n6_9] using valueLocal
  have enteredInvariant := invariant.after_read state s7 keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨post,tail,header,agreement,cost,remaining,preserved,globals,code,domain,endian⟩ :=
    evaluate_hashInsert_hash_values_inKU s7 capacity used table values value order orderPos count keys stride key keyLength bits supported
      tableBinding orderBinding orderPosBinding valueBinding capBinding usedBinding keysBinding strideBinding keyBinding klenBinding
      budget enteredInvariant sourceAligned len8 keyFit sourceWordDomain sourceByteDomain keysBeforeValues
      targets (entries.after_read rfl rfl rfl) member
  rw [source_htabInsert_header_prefix,run1]
  dsimp only
  rw [run2]
  dsimp only
  rw [run3]
  dsimp only
  rw [run4]
  dsimp only
  rw [run5]
  dsimp only
  rw [run6]
  dsimp only
  rw [run7]
  dsimp only
  rw [tail]
  refine ⟨_,rfl,header,agreement,cost,remaining,?_,globals,code,domain,endian⟩
  · exact preserved.after_read rfl rfl rfl


/-- The actual supported-width insertion preserves registered-pointer
membership through hashing, probing, copy, stores, and caller scope restoration. -/
theorem evaluate_hashInsert_call_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (capacity used table values value order orderPos count keys stride key keyLength : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
      [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      HashTableValuesIn table targets post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryInvariant := invariant.after_read state entry keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨post,body,header,agreement,cost,remaining,preserved,globals,code,domain,endian⟩ :=
    evaluate_source_hashInsert_values_inKU entry capacity used table values value order orderPos count keys stride key keyLength bits supported
      t v k (by change capacity.toNat + keyLength.toNat + 2 ≤ state.clock - 1; omega)
      entryInvariant sourceAligned len8 keyFit sourceWordDomain sourceByteDomain keysBeforeValues
      targets (entries.after_read rfl rfl rfl) member
  have installed : state.code.lookup (ofString "htab_insert_raw") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_insert_raw,.one) := by
    rw [invariant.code]; exact originalRuntimeCode_hashInsert_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_insert_raw")
    (ofString "t") (ofString "key") (ofString "value") (sourceFunctionBody Guest.guestFn_htab_insert_raw)
    table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_insert_raw")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_insert_raw) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,header,agreement,?_,?_,?_,globals,code,domain,endian,rfl⟩
  · change state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3
    change state.clock - 1 ≤ post.clock + capacity.toNat + keyLength.toNat + 2 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · exact preserved.after_read rfl rfl rfl


#print axioms evaluate_hashInsert_hash_values_inKU
#print axioms evaluate_source_hashInsert_values_inKU
#print axioms evaluate_hashInsert_call_values_inKU
end InitECandidate.Runtime
