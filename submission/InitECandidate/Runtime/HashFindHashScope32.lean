import InitECandidate.Runtime.HashCall32
import InitECandidate.Runtime.HashFindHashEnvironment
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashFindHashScope : ProgHOL 64 :=
  .decCall (ofString "h") .one (ofString "htab_hash")
    [.var .local (ofString "key"),.var .local (ofString "klen")] hashFindIndexScope

theorem source_htabFind_header_prefix : sourceFunctionBody Guest.guestFn_htab_find_slot =
    .dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
      (.dec (ofString "klen") .one (.load .one (hashLocalAddress (ofString "t") 0))
        (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8))
          (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32))
            (.dec (ofString "used") .one (.load .one (hashLocalAddress (ofString "t") 48)) hashFindHashScope)))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual hash call, masked-index scope and complete lookup loop/return.
The hash call adds one clock to the twice-capacity loop bound. -/
theorem evaluate_hashFindHashScope32 {F : Type} (keys stride key capacity used : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment32 keys stride key capacity used state)
    (budget : 2 * capacity.toNat + 1 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindHashScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word key),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,ready.keyLocal,ready.lengthLocal]
  obtain ⟨hash,hashed,clock,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hash32_declaration state _ _ key arguments ready.code (by omega) keyAligned ready.keyDomain
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have environment : HashFindEnvironment32 keys stride key capacity used entered :=
    HashFindEnvironment32.after_hash keys stride key capacity used hash state entered ready memory code addresses endian
      (by simp only [entered,setVarHOLFinite,locals])
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ticks : entered.clock = state.clock - 1 := clock
  obtain ⟨found,post,tail,inside,cost,remaining,tailMemory,tailGlobals,tailCode,tailAddresses,tailEndian⟩ := evaluate_hashFindIndexScope32_from_count keys stride key capacity used hash
    bits power keysAligned strideAligned keyAligned strideFits bounded entered environment h (by omega)
  unfold hashFindHashScope
  rw [decl]
  change ∃ found post, (let output := evaluateHOLFiniteState entered hashFindIndexScope; _) = _ ∧ _
  rw [tail]
  exact ⟨found,_,rfl,inside,by change state.clock ≤ post.clock + 2 * capacity.toNat + 1; omega,
    by change post.clock ≤ state.clock; omega,tailMemory.trans memory,tailGlobals.trans globals,tailCode.trans code,tailAddresses.trans addresses,tailEndian.trans endian⟩

#print axioms source_htabFind_header_prefix
#print axioms evaluate_hashFindHashScope32
end InitECandidate.Runtime
