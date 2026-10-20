import InitECandidate.Runtime.CrepExpressionWork
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-- Payload words returned through a Crep call boundary. -/
def crepCallPayloadWords : Option (CrepResultHOLExact 64) → Nat
  | some (.return values) => values.length
  | _ => 0

/-- Executed Crep work. Each executed statement pays one unit and each
evaluated expression pays its scalar node work. Recursive rules follow the
exact evaluator's successor states: only the selected branch, every loop guard,
the actual callee body and a matched handler are charged. Failing guards and
operations keep the work of the expressions already evaluated. This is a count
of Crep execution events, not yet of RISC-V instructions. -/
inductive CrepWork {σ : Type} : CrepSemHOLState 64 σ → CrepProgHOL 64 → Nat → Prop where
  | skip (t) : CrepWork t .skip 1
  | tick (t) : CrepWork t .tick 1
  | breakStmt (t label) : CrepWork t (.break label) 1
  | continueStmt (t label) : CrepWork t (.continue label) 1
  | raise (t code) : CrepWork t (.raise code) 1
  | assign (t name value) : CrepWork t (.assign name value) (1 + crepNodeWork value)
  | storeGlob (t address value) :
      CrepWork t (.storeGlob address value) (1 + crepNodeWork value)
  | store (t address value) :
      CrepWork t (.store address value) (1 + crepNodeWork address + crepNodeWork value)
  | store32 (t address value) :
      CrepWork t (.store32 address value) (1 + crepNodeWork address + crepNodeWork value)
  | storeByte (t address value) :
      CrepWork t (.storeByte address value) (1 + crepNodeWork address + crepNodeWork value)
  | returnStmt (t values) :
      CrepWork t (.return values) (1 + crepListWork values + values.length)
  | primitive (t names operator args) :
      CrepWork t (.primitive names operator args) (1 + names.length + args.length)
  | shMem (t operator name address) :
      CrepWork t (.shMem operator name address) (1 + crepNodeWork address)
  | extCall (t function configuration configurationLength array arrayLength) :
      CrepWork t (.extCall function configuration configurationLength array arrayLength) 1
  | decFailure {t name value body} (failed : evalCrepSemHOLExp t value = none) :
      CrepWork t (.dec name value body) (1 + crepNodeWork value)
  | dec {t name value body word bodyWork}
      (evaluated : evalCrepSemHOLExp t value = some word)
      (bodyRun : CrepWork { t with locals := t.locals.updateEq (name, word) } body bodyWork) :
      CrepWork t (.dec name value body) (1 + crepNodeWork value + bodyWork)
  | seqNext {t first second middle firstWork secondWork}
      (one : CrepWork t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (none, middle))
      (two : CrepWork middle second secondWork) :
      CrepWork t (.seq first second) (1 + firstWork + secondWork)
  | seqStop {t first second result middle firstWork}
      (one : CrepWork t first firstWork)
      (run : evalCrepSemHOLProgExact t first = (some result, middle)) :
      CrepWork t (.seq first second) (1 + firstWork)
  | iteBranch {t condition yes no word branchWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word))
      (branch : CrepWork t (if word ≠ 0 then yes else no) branchWork) :
      CrepWork t (.ite condition yes no) (1 + crepNodeWork condition + branchWork)
  | iteInvalid {t condition yes no}
      (invalid : ∀ word, evalCrepSemHOLExp t condition ≠ some (.word word)) :
      CrepWork t (.ite condition yes no) (1 + crepNodeWork condition)
  | whileExit {t condition body}
      (exit : ∀ word, evalCrepSemHOLExp t condition = some (.word word) → word = 0) :
      CrepWork t (.while condition body) (1 + crepNodeWork condition)
  | whileTimeout {t condition body word}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock = 0) :
      CrepWork t (.while condition body) (1 + crepNodeWork condition)
  | whileLoop {t condition body word bodyWork result middle restWork}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWork (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (again : result = none ∨ result = some (.continue 0))
      (rest : CrepWork middle (.while condition body) restWork) :
      CrepWork t (.while condition body) (1 + crepNodeWork condition + bodyWork + restWork)
  | whileStop {t condition body word bodyWork result middle}
      (guard : evalCrepSemHOLExp t condition = some (.word word)) (nonzero : word ≠ 0)
      (clock : t.clock ≠ 0)
      (one : CrepWork (decClockCrepSemHOL t) body bodyWork)
      (run : evalCrepSemHOLProgExact (decClockCrepSemHOL t) body = (result, middle))
      (stop : result ≠ none ∧ result ≠ some (.continue 0)) :
      CrepWork t (.while condition body) (1 + crepNodeWork condition + bodyWork)
  /-- Argument failure, lookup failure, return-name rejection or timeout. -/
  | callShort {t returnInfo function arguments}
      (short : arguments.mapM (evalCrepSemHOLExp t) = none ∨
        ∃ values, arguments.mapM (evalCrepSemHOLExp t) = some values ∧
          (lookupCodeFiniteHOL t.code function values values.length = none ∨
            crepReturnInfoNodupError returnInfo ∨ t.clock = 0)) :
      CrepWork t (.call returnInfo function arguments) (1 + crepListWork arguments)
  | callBody {t returnInfo function arguments values body locals bodyWork result post}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : ¬ crepReturnInfoNodupError returnInfo)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWork { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (result, post))
      (unhandled : ∀ code rts handler, result = some (.exception code) →
        returnInfo ≠ some (rts, some (code, handler))) :
      CrepWork t (.call returnInfo function arguments)
        (1 + crepListWork arguments + values.length + bodyWork + crepCallPayloadWords result)
  | callHandler {t rts code handler function arguments values body locals bodyWork post
      handlerWork}
      (args : arguments.mapM (evalCrepSemHOLExp t) = some values)
      (lookup : lookupCodeFiniteHOL t.code function values values.length = some (body, locals))
      (names : rts.Nodup)
      (clock : t.clock ≠ 0)
      (bodyRun : CrepWork { decClockCrepSemHOL t with locals := locals } body bodyWork)
      (run : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
        (some (.exception code), post))
      (handlerRun : CrepWork { post with locals := t.locals } handler handlerWork) :
      CrepWork t (.call (some (rts, some (code, handler))) function arguments)
        (1 + crepListWork arguments + values.length + bodyWork + handlerWork)

/-- Every executed Crep statement pays at least its entry unit. -/
theorem CrepWork.entry {σ : Type} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {w : Nat}
    (run : CrepWork t p w) : 1 ≤ w := by
  cases run <;> omega

#print axioms CrepWork.entry
end InitECandidate.Runtime.FineCost
