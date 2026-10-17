import InitECandidate.Runtime.HashDeleteHash32
import InitECandidate.Runtime.HashCallSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_hash_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride keyLength : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : (keys + index * stride).toNat % 8 = 0)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (words : ∀ offset : Nat, offset < keyLength.toNat →
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat →
      state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))) :
    ∃ hash : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState state hashDeleteLoopRest =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "h") (.val (.word hash)) ready)
          hashDeleteAfterHash;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "h",state.locals.lookup (ofString "h")))})) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "keys"),
        .panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] =
      some [.val (.word (keys + index * stride)),.val (.word keyLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,keysLocal,indexLocal,strideLocal,lengthLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hash_supported_declaration state _ _ (keys + index * stride) keyLength arguments code clock aligned supported words bytes
  refine ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,?_⟩
  rw [source_hashDelete_hash_scope]
  exact decl _ _


#print axioms evaluate_hashDelete_hash_supported
end InitECandidate.Runtime
