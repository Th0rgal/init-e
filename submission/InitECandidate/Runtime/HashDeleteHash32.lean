import InitECandidate.Runtime.HashDeleteOccupiedSelection
import InitECandidate.Runtime.HashCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteAfterHash : ProgHOL 64 :=
  match hashDeleteLoopRest with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_hashDelete_hash_scope : hashDeleteLoopRest =
    .decCall (ofString "h") .one (ofString "htab_hash")
      [.op .add [.var .local (ofString "keys"),
        .panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] hashDeleteAfterHash := by
  unfold hashDeleteAfterHash hashDeleteLoopRest
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]

/-- The occupied deletion path hashes the actual scanned key, spends one
call clock, and preserves memory and caller locals before move selection. -/
theorem evaluate_hashDelete_hash32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : (keys + index * stride).toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset)) :
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
      some [.val (.word (keys + index * stride)),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,keysLocal,indexLocal,strideLocal,lengthLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,decl⟩ :=
    evaluate_hash32_declaration state _ _ (keys + index * stride) arguments code clock aligned domain
  refine ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,?_⟩
  rw [source_hashDelete_hash_scope]
  exact decl _ _

#print axioms source_hashDelete_hash_scope
#print axioms evaluate_hashDelete_hash32
end InitECandidate.Runtime
