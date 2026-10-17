import InitECandidate.Runtime.HashDeleteSavedScopeValuesIn
import InitECandidate.Runtime.HashDeleteHeaderScopesLinked32
import InitECandidate.Runtime.HeaderLoadScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.delete_header_scopes_from_hole_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (holeInside : hole.toNat < capacity.toNat)
    (holeOccupied : hashOccupancyRead state used hole ≠ some 0)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post,
      evaluateHOLFiniteState state hashDeleteFoundHeaderScopes = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have ne0_1 : ofString "klen" ≠ ofString "stride" := by decide
  have ne0_2 : ofString "klen" ≠ ofString "keys" := by decide
  have ne0_3 : ofString "klen" ≠ ofString "vals" := by decide
  have ne0_4 : ofString "klen" ≠ ofString "used" := by decide
  have ne0_5 : ofString "klen" ≠ ofString "order" := by decide
  have ne0_6 : ofString "klen" ≠ ofString "order_pos" := by decide
  have ne0_7 : ofString "klen" ≠ ofString "t" := by decide
  have ne0_8 : ofString "klen" ≠ ofString "i" := by decide
  have ne0_9 : ofString "klen" ≠ ofString "cap" := by decide
  have ne1_0 : ofString "stride" ≠ ofString "klen" := by decide
  have ne1_2 : ofString "stride" ≠ ofString "keys" := by decide
  have ne1_3 : ofString "stride" ≠ ofString "vals" := by decide
  have ne1_4 : ofString "stride" ≠ ofString "used" := by decide
  have ne1_5 : ofString "stride" ≠ ofString "order" := by decide
  have ne1_6 : ofString "stride" ≠ ofString "order_pos" := by decide
  have ne1_7 : ofString "stride" ≠ ofString "t" := by decide
  have ne1_8 : ofString "stride" ≠ ofString "i" := by decide
  have ne1_9 : ofString "stride" ≠ ofString "cap" := by decide
  have ne2_0 : ofString "keys" ≠ ofString "klen" := by decide
  have ne2_1 : ofString "keys" ≠ ofString "stride" := by decide
  have ne2_3 : ofString "keys" ≠ ofString "vals" := by decide
  have ne2_4 : ofString "keys" ≠ ofString "used" := by decide
  have ne2_5 : ofString "keys" ≠ ofString "order" := by decide
  have ne2_6 : ofString "keys" ≠ ofString "order_pos" := by decide
  have ne2_7 : ofString "keys" ≠ ofString "t" := by decide
  have ne2_8 : ofString "keys" ≠ ofString "i" := by decide
  have ne2_9 : ofString "keys" ≠ ofString "cap" := by decide
  have ne3_0 : ofString "vals" ≠ ofString "klen" := by decide
  have ne3_1 : ofString "vals" ≠ ofString "stride" := by decide
  have ne3_2 : ofString "vals" ≠ ofString "keys" := by decide
  have ne3_4 : ofString "vals" ≠ ofString "used" := by decide
  have ne3_5 : ofString "vals" ≠ ofString "order" := by decide
  have ne3_6 : ofString "vals" ≠ ofString "order_pos" := by decide
  have ne3_7 : ofString "vals" ≠ ofString "t" := by decide
  have ne3_8 : ofString "vals" ≠ ofString "i" := by decide
  have ne3_9 : ofString "vals" ≠ ofString "cap" := by decide
  have ne4_0 : ofString "used" ≠ ofString "klen" := by decide
  have ne4_1 : ofString "used" ≠ ofString "stride" := by decide
  have ne4_2 : ofString "used" ≠ ofString "keys" := by decide
  have ne4_3 : ofString "used" ≠ ofString "vals" := by decide
  have ne4_5 : ofString "used" ≠ ofString "order" := by decide
  have ne4_6 : ofString "used" ≠ ofString "order_pos" := by decide
  have ne4_7 : ofString "used" ≠ ofString "t" := by decide
  have ne4_8 : ofString "used" ≠ ofString "i" := by decide
  have ne4_9 : ofString "used" ≠ ofString "cap" := by decide
  have ne5_0 : ofString "order" ≠ ofString "klen" := by decide
  have ne5_1 : ofString "order" ≠ ofString "stride" := by decide
  have ne5_2 : ofString "order" ≠ ofString "keys" := by decide
  have ne5_3 : ofString "order" ≠ ofString "vals" := by decide
  have ne5_4 : ofString "order" ≠ ofString "used" := by decide
  have ne5_6 : ofString "order" ≠ ofString "order_pos" := by decide
  have ne5_7 : ofString "order" ≠ ofString "t" := by decide
  have ne5_8 : ofString "order" ≠ ofString "i" := by decide
  have ne5_9 : ofString "order" ≠ ofString "cap" := by decide
  have ne6_0 : ofString "order_pos" ≠ ofString "klen" := by decide
  have ne6_1 : ofString "order_pos" ≠ ofString "stride" := by decide
  have ne6_2 : ofString "order_pos" ≠ ofString "keys" := by decide
  have ne6_3 : ofString "order_pos" ≠ ofString "vals" := by decide
  have ne6_4 : ofString "order_pos" ≠ ofString "used" := by decide
  have ne6_5 : ofString "order_pos" ≠ ofString "order" := by decide
  have ne6_7 : ofString "order_pos" ≠ ofString "t" := by decide
  have ne6_8 : ofString "order_pos" ≠ ofString "i" := by decide
  have ne6_9 : ofString "order_pos" ≠ ofString "cap" := by decide
  have ne7_0 : ofString "t" ≠ ofString "klen" := by decide
  have ne7_1 : ofString "t" ≠ ofString "stride" := by decide
  have ne7_2 : ofString "t" ≠ ofString "keys" := by decide
  have ne7_3 : ofString "t" ≠ ofString "vals" := by decide
  have ne7_4 : ofString "t" ≠ ofString "used" := by decide
  have ne7_5 : ofString "t" ≠ ofString "order" := by decide
  have ne7_6 : ofString "t" ≠ ofString "order_pos" := by decide
  have ne7_8 : ofString "t" ≠ ofString "i" := by decide
  have ne7_9 : ofString "t" ≠ ofString "cap" := by decide
  have ne8_0 : ofString "i" ≠ ofString "klen" := by decide
  have ne8_1 : ofString "i" ≠ ofString "stride" := by decide
  have ne8_2 : ofString "i" ≠ ofString "keys" := by decide
  have ne8_3 : ofString "i" ≠ ofString "vals" := by decide
  have ne8_4 : ofString "i" ≠ ofString "used" := by decide
  have ne8_5 : ofString "i" ≠ ofString "order" := by decide
  have ne8_6 : ofString "i" ≠ ofString "order_pos" := by decide
  have ne8_7 : ofString "i" ≠ ofString "t" := by decide
  have ne8_9 : ofString "i" ≠ ofString "cap" := by decide
  have ne9_0 : ofString "cap" ≠ ofString "klen" := by decide
  have ne9_1 : ofString "cap" ≠ ofString "stride" := by decide
  have ne9_2 : ofString "cap" ≠ ofString "keys" := by decide
  have ne9_3 : ofString "cap" ≠ ofString "vals" := by decide
  have ne9_4 : ofString "cap" ≠ ofString "used" := by decide
  have ne9_5 : ofString "cap" ≠ ofString "order" := by decide
  have ne9_6 : ofString "cap" ≠ ofString "order_pos" := by decide
  have ne9_7 : ofString "cap" ≠ ofString "t" := by decide
  have ne9_8 : ofString "cap" ≠ ofString "i" := by decide
  have domains := invariant.header_domain state keyLength table keys stride capacity used values order orderPos items bits
  let s1 := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) state
  have t1 : state.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s2 := setVarHOLFinite (ofString "stride") (.val (.word stride)) s1
  have t2 : s1.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s3 := setVarHOLFinite (ofString "keys") (.val (.word keys)) s2
  have t3 : s2.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s4 := setVarHOLFinite (ofString "vals") (.val (.word values)) s3
  have t4 : s3.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s5 := setVarHOLFinite (ofString "used") (.val (.word used)) s4
  have t5 : s4.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s6 := setVarHOLFinite (ofString "order") (.val (.word order)) s5
  have t6 : s5.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  let s7 := setVarHOLFinite (ofString "order_pos") (.val (.word orderPos)) s6
  have t7 : s6.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [s1,s2,s3,s4,s5,s6,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne0_1,ne0_2,ne0_3,ne0_4,ne0_5,ne0_6,ne0_7,ne0_8,ne0_9,ne1_0,ne1_2,ne1_3,ne1_4,ne1_5,ne1_6,ne1_7,ne1_8,ne1_9,ne2_0,ne2_1,ne2_3,ne2_4,ne2_5,ne2_6,ne2_7,ne2_8,ne2_9,ne3_0,ne3_1,ne3_2,ne3_4,ne3_5,ne3_6,ne3_7,ne3_8,ne3_9,ne4_0,ne4_1,ne4_2,ne4_3,ne4_5,ne4_6,ne4_7,ne4_8,ne4_9,ne5_0,ne5_1,ne5_2,ne5_3,ne5_4,ne5_6,ne5_7,ne5_8,ne5_9,ne6_0,ne6_1,ne6_2,ne6_3,ne6_4,ne6_5,ne6_7,ne6_8,ne6_9,ne7_0,ne7_1,ne7_2,ne7_3,ne7_4,ne7_5,ne7_6,ne7_8,ne7_9,ne8_0,ne8_1,ne8_2,ne8_3,ne8_4,ne8_5,ne8_6,ne8_7,ne8_9,ne9_0,ne9_1,ne9_2,ne9_3,ne9_4,ne9_5,ne9_6,ne9_7,ne9_8] using tableLocal
  have other : ∀ name, name ≠ ofString "klen" → name ≠ ofString "stride" → name ≠ ofString "keys" → name ≠ ofString "vals" → name ≠ ofString "used" → name ≠ ofString "order" → name ≠ ofString "order_pos" → s7.locals.lookup name = state.locals.lookup name := by
    intro name a b c d e f g
    simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e,Ne.symm f,Ne.symm g]
  have enteredInvariant := invariant.after_read state s7 keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  obtain ⟨post,tail,postRegistered,cost,remaining,globals,code,domain,endian⟩ := enteredInvariant.delete_saved_scope_from_hole_values_in s7 keyLength table keys stride capacity used values order orderPos items hole bits
    (entries.after_read state s7 used values capacity rfl rfl rfl) (reverse.after_read state s7 used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state s7 order capacity items rfl) keyValueOrder holeInside holeOccupied
    ((other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans holeLocal)
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne3_2,ne4_2,ne5_2,ne6_2])
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne2_1,ne3_1,ne4_1,ne5_1,ne6_1])
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne1_0,ne2_0,ne3_0,ne4_0,ne5_0,ne6_0])
    ((other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans capacityLocal)
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne5_4,ne6_4])
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne4_3,ne5_3,ne6_3])
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne6_5])
    (by simp [s1,s2,s3,s4,s5,s6,s7,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (linked.after_read state s7 used order orderPos capacity items rfl rfl rfl)
    ((other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tableLocal) supported targets (registered.after_read rfl rfl rfl) budget
  unfold hashDeleteFoundHeaderScopes
  rw [evaluate_header_load_scope state (ofString "klen") (ofString "t") table 0 keyLength _ t1 (domains 0 (by decide)) invariant.cell0]
  dsimp only
  rw [evaluate_header_load_scope s1 (ofString "stride") (ofString "t") table 8 stride _ t2 (domains 8 (by decide)) invariant.cell8]
  dsimp only
  rw [evaluate_header_load_scope s2 (ofString "keys") (ofString "t") table 32 keys _ t3 (domains 32 (by decide)) invariant.cell32]
  dsimp only
  rw [evaluate_header_load_scope s3 (ofString "vals") (ofString "t") table 40 values _ t4 (domains 40 (by decide)) invariant.cell40]
  dsimp only
  rw [evaluate_header_load_scope s4 (ofString "used") (ofString "t") table 48 used _ t5 (domains 48 (by decide)) invariant.cell48]
  dsimp only
  rw [evaluate_header_load_scope s5 (ofString "order") (ofString "t") table 56 order _ t6 (domains 56 (by decide)) invariant.cell56]
  dsimp only
  rw [evaluate_header_load_scope s6 (ofString "order_pos") (ofString "t") table 64 orderPos _ t7 (domains 64 (by decide)) invariant.cell64]
  dsimp only
  rw [tail]
  exact ⟨_,rfl,postRegistered.after_read rfl rfl rfl,cost,remaining,globals,code,domain,endian⟩

#print axioms HashTableArraysInvariant.delete_header_scopes_from_hole_values_in
end InitECandidate.Runtime
