import InitECandidate.Runtime.CrepExpressionWork
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-- Payload words returned through a Crep call boundary. -/
def crepCallPayloadWords : Option (CrepResultHOLExact 64) → Nat
  | some (.return values) => values.length
  | _ => 0

/-- Executed Crep work, parametrized by the price of each evaluated
expression (`price`) and argument list (`priceList`). Each executed statement pays one unit and each
evaluated expression pays its scalar node work. Recursive rules follow the
exact evaluator's successor states: only the selected branch, every loop guard,
the actual callee body and a matched handler are charged. Failing guards and
operations keep the work of the expressions already evaluated. This is a count
of Crep execution events. An assignment or declaration costs exactly its
expression price (it compiles to a single Loop assignment). `Seq` is structural
composition and carries no local charge. -/
inductive CrepWorkP (price : CrepExpHOL 64 → Nat) (priceList : List (CrepExpHOL 64) → Nat)
    (unit prim call ret : Nat) {σ : Type} :
    CrepSemHOLState 64 σ → CrepProgHOL 64 → Nat → Prop where
  | skip (t) : CrepWorkP price priceList unit prim call ret t .skip 0
  | tick (t) : CrepWorkP price priceList unit prim call ret t .tick unit
  | breakStmt (t label) : CrepWorkP price priceList unit prim call ret t (.break label) unit
  | continueStmt (t label) : CrepWorkP price priceList unit prim call ret t (.continue label) unit
  | raise (t code) : CrepWorkP price priceList unit prim call ret t (.raise code) (prim + 1)
  | assign (t name value) : CrepWorkP price priceList unit prim call ret t (.assign name value) (price value)
  | storeGlob (t address value) :
      CrepWorkP price priceList unit prim call ret t (.storeGlob address value) (unit + price value)
  | store (t address value) :
      CrepWorkP price priceList unit prim call ret t (.store address value) (unit + price address + price value)
  | store32 (t address value) :
      CrepWorkP price priceList unit prim call ret t (.store32 address value) (unit + price address + price value)
  | storeByte (t address value) :
      CrepWorkP price priceList unit prim call ret t (.storeByte address value) (unit + price address + price value)
  | returnStmt (t values) :
      CrepWorkP price priceList unit prim call ret t (.return values) (unit + priceList values + values.length)
  | primitive (t names operator args) :
      CrepWorkP price priceList unit prim call ret t (.primitive names operator args) (prim + names.length + args.length)
  | shMem (t operator name address) :
      CrepWorkP price priceList unit prim call ret t (.shMem operator name address) (unit + price address)
  | extCall (t function configuration configurationLength array arrayLength) :
      CrepWorkP price priceList unit prim call ret t (.extCall function configuration configurationLength array arrayLength) unit
  | decFailure {t name value body} (failed : evalCrepSemHOLExp t value = none) :
      CrepWorkP price priceList unit prim call ret t (.dec name value body) (price value)
  | dec {t name value body word bodyWork}
      (evaluated : evalCrepSemHOLExp t value = some word)
      (bodyRun : CrepWorkP price priceList unit prim call ret { t with locals := t.locals.updateEq (name, word) } body bodyWork) :
      CrepWorkP price priceList unit prim call ret t (.dec name value body) (price value + bodyWork)
  | seqNext {t first second middle firstWork secondWork}
      (one : CrepWorkP price priceList unit prim call ret t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (none, middle))
      (two : CrepWorkP price priceList unit prim call ret middle second secondWork) :
      CrepWorkP price priceList unit prim call ret t (.seq first second) (firstWork + secondWork)
  | seqStop {t first second result middle firstWork}
      (one : CrepWorkP price priceList unit prim call ret t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (some result, middle)) :
      CrepWorkP price priceList unit prim call ret t (.seq first second) firstWork
  | iteBranch {t condition yes no word branchWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word))
      (branch : CrepWorkP price priceList unit prim call ret t (if word ≠ 0 then yes else no) branchWork) :
      CrepWorkP price priceList unit prim call ret t (.ite condition yes no) (unit + price condition + branchWork)
  | iteInvalid {t condition yes no}
      (invalid : ∀ word, evalCrepSemHOLExp t condition ≠ some (.word word)) :
      CrepWorkP price priceList unit prim call ret t (.ite condition yes no) (unit + price condition)
  | whileExit {t condition body}
      (exit : ∀ word, evalCrepSemHOLExp t condition = some (.word word) → word = 0) :
      CrepWorkP price priceList unit prim call ret t (.while condition body) (unit + unit + unit + price condition)
  | whileTimeout {t condition body word}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock = 0) :
      CrepWorkP price priceList unit prim call ret t (.while condition body) (unit + unit + unit + price condition)
  | whileLoop {t condition body word bodyWork result middle restWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkP price priceList unit prim call ret (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (again : result = none ∨ result = some (.continue 0))
      (rest : CrepWorkP price priceList unit prim call ret middle (.while condition body) restWork) :
      CrepWorkP price priceList unit prim call ret t (.while condition body) (unit + unit + unit + price condition + bodyWork + restWork)
  | whileStop {t condition body word bodyWork result middle}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWorkP price priceList unit prim call ret (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (stop : result ≠ none ∧ result ≠ some (.continue 0)) :
      CrepWorkP price priceList unit prim call ret t (.while condition body) (unit + unit + unit + price condition + bodyWork)
  /-- Argument failure, lookup failure, return-name rejection or timeout. -/
  | callShort {t returnInfo function arguments}
      (short : arguments.mapM (evalCrepSemHOLExp t) = none ∨
        ∃ values, arguments.mapM (evalCrepSemHOLExp t) = some values ∧
          (lookupCodeFiniteHOL t.code function values values.length = none ∨
            crepReturnInfoNodupError returnInfo ∨ t.clock = 0)) :
      CrepWorkP price priceList unit prim call ret t (.call returnInfo function arguments)
        (call + priceList arguments)
  | callBody {t returnInfo function arguments values body locals bodyWork result post}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : ¬ crepReturnInfoNodupError returnInfo)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkP price priceList unit prim call ret { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (result, post))
      (unhandled : ∀ code rts handler, result = some (.exception code) →
        returnInfo ≠ some (rts, some (code, handler))) :
      CrepWorkP price priceList unit prim call ret t (.call returnInfo function arguments)
        (call + priceList arguments + values.length + bodyWork +
          ret * crepCallPayloadWords result)
  | callHandler {t rts code handler function arguments values body locals bodyWork post
      handlerWork}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : rts.Nodup)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWorkP price priceList unit prim call ret { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (some (.exception code), post))
      (handlerRun : CrepWorkP price priceList unit prim call ret { post with locals := t.locals } handler handlerWork) :
      CrepWorkP price priceList unit prim call ret t (.call (some (rts, some (code, handler))) function arguments)
        (call + priceList arguments + values.length + bodyWork + handlerWork)


/-- Executed Crep work at the node-count price used by the Pan-to-Crep transfer. -/
abbrev CrepWork {σ : Type} := @CrepWorkP crepNodeWork crepListWork 1 1 3 1 σ

abbrev CrepWork.skip {σ : Type} := @CrepWorkP.skip crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.tick {σ : Type} := @CrepWorkP.tick crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.breakStmt {σ : Type} := @CrepWorkP.breakStmt crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.continueStmt {σ : Type} := @CrepWorkP.continueStmt crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.raise {σ : Type} := @CrepWorkP.raise crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.assign {σ : Type} := @CrepWorkP.assign crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.storeGlob {σ : Type} := @CrepWorkP.storeGlob crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.store {σ : Type} := @CrepWorkP.store crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.store32 {σ : Type} := @CrepWorkP.store32 crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.storeByte {σ : Type} := @CrepWorkP.storeByte crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.returnStmt {σ : Type} := @CrepWorkP.returnStmt crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.primitive {σ : Type} := @CrepWorkP.primitive crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.shMem {σ : Type} := @CrepWorkP.shMem crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.extCall {σ : Type} := @CrepWorkP.extCall crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.decFailure {σ : Type} := @CrepWorkP.decFailure crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.dec {σ : Type} := @CrepWorkP.dec crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.seqNext {σ : Type} := @CrepWorkP.seqNext crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.seqStop {σ : Type} := @CrepWorkP.seqStop crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.iteBranch {σ : Type} := @CrepWorkP.iteBranch crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.iteInvalid {σ : Type} := @CrepWorkP.iteInvalid crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.whileExit {σ : Type} := @CrepWorkP.whileExit crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.whileTimeout {σ : Type} := @CrepWorkP.whileTimeout crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.whileLoop {σ : Type} := @CrepWorkP.whileLoop crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.whileStop {σ : Type} := @CrepWorkP.whileStop crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.callShort {σ : Type} := @CrepWorkP.callShort crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.callBody {σ : Type} := @CrepWorkP.callBody crepNodeWork crepListWork 1 1 3 1 σ
abbrev CrepWork.callHandler {σ : Type} := @CrepWorkP.callHandler crepNodeWork crepListWork 1 1 3 1 σ

#print axioms CrepWorkP
end InitECandidate.Runtime.FineCost
