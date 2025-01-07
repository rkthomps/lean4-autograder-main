
import Lean
import AutograderLib
open Lean IO System Elab Command Meta Lean.Meta Lean.Elab.Tactic

-- Used for non-exercise-specific results (e.g., global failures)
structure FailureResult where
  output : String
  score : Float := 0.0
  output_format : String := "text"
  deriving ToJson

-- Used for exercise-specific results
structure ExerciseResult where
  name : Name
  score : Float
  maxScore : Float
  status : String
  output : String
  deriving ToJson

def ExerciseResult.print (er : ExerciseResult) : IO Unit := do
  let score :=
    match JsonNumber.fromFloat? er.score with
    | Sum.inl e => Json.str e
    | Sum.inr n => Json.num n
  IO.println s!"{er.name}:"
  IO.println s!"  {er.status} ({score} points)"
  IO.println s!"  {er.output}"

structure ExerciseResultDebug extends ExerciseResult where
  sheet_name : Name         -- Name of the exercise in the sheet
  expected_status : String  -- Expected status of the test, "passed" or "failed"
  output_log : String       -- Additional information about the autograder's decision

inductive Color : Type
  | red
  | green

def addANSICode (c : Color) (s : String) : String :=
  let code := match c with
    | .red => "31"
    | .green => "32"
  s!"\x1b[1m\u001b[{code}m{s}\u001b[0m"

def ExerciseResultDebug.print (er : ExerciseResultDebug) : IO Unit := do
  IO.print s!"{er.name}: "
  if er.status == er.expected_status then
    IO.println (addANSICode Color.green "Passed")
  else
    IO.println (addANSICode Color.red "Failed")
  IO.println s!"  {er.output_log}"

structure GradingResults where
  tests : Array ExerciseResult
  output: String
  output_format: String := "text"
  deriving ToJson

def GradingResults.print (gr : GradingResults) : IO Unit := do
  IO.println gr.output
  for er in gr.tests do
    er.print
    IO.println ""

def Lean.Environment.moduleDataOf? (module : Name) (env : Environment)
  : Option ModuleData := do
  let modIdx : Nat ← env.getModuleIdx? module
  env.header.moduleData[modIdx]?

def Lean.Environment.moduleOfDecl? (decl : Name) (env : Environment)
  : Option Name := do
  let modIdx : Nat ← env.getModuleIdxFor? decl
  env.header.moduleNames[modIdx]?

def defaultValidAxioms : Array Name :=
  #["Classical.choice".toName,
    "Quot.sound".toName,
    "propext".toName,
    "funext".toName]

def axiomHasCorrectType (ax : Name) (sheet submission : Environment) : Bool :=
  match (sheet.find? ax, submission.find? ax) with
    | (some sheetConst, some subConst) => sheetConst.type == subConst.type
    | _                                => false

def findInvalidAxiom (submissionAxioms : List Name)
                     (sheet submission : Environment)
                     (validAxioms : Array Name) : Option Name := do
  for ax in submissionAxioms do
    let isBaseAxiom := validAxioms.contains ax
    let isTaggedAxiom := legalAxiomAttr.hasTag sheet ax
    let isTypeCorrect := axiomHasCorrectType ax sheet submission

    -- If the axiom is not one of our predefined acceptable axioms, and is
    -- also not tagged in the stencil as legal, then it's invalid
    if ! (isBaseAxiom || isTaggedAxiom) || ! isTypeCorrect then
      return ax
  none

-- Source: aesop/Aesop/Util/Basic.lean
def runTacticMAsMetaM {α : Type} (tactic : TacticM α) (goals : List MVarId) :
    MetaM (α × List MVarId) := do
  let (a, s) ← tactic |>.run { elaborator := .anonymous } |>.run { goals } |>.run'
  return (a, s.goals)

-- Ideally, we could format our Gradescope output nicely as HTML and escape
-- inserted file names/error messages/etc. Unfortunately, Gradescope doesn't
-- handle pre-escaped HTML well (it tries to re-escape it), so until a
-- workaround for that issue is found, we'll stick with plain text.
def escapeHtml (s : String) :=
  [("<", "&lt;"), (">", "&gt;"), ("&", "&amp;"), ("\"", "&quot;")].foldl
    (λ acc (char, repl) => acc.replace char repl) s

-- Throw error and show it to the student, optionally providing additional
-- information for the instructor only
def exitWithError {α} (errMsg : String) (instructorInfo: String := "")
  : IO α := do
  -- let result : FailureResult := {output := errMsg}
  -- IO.FS.writeFile resultsJsonPath (toJson result).pretty
  throw <| IO.userError (errMsg ++ "\n" ++ instructorInfo)


def checkDefinition (name subName : Name) (pts : Float) (constInfo subConstInfo : ConstantInfo)
  (sheet : Environment) : IO ExerciseResultDebug := do
    -- Get the list of tactics for the problem
    let tactics :=
      if let some t := validTacticsAttr.getParam? sheet name then t
      else if let some d := defaultTacticsAttr.getParam? sheet `setDefaultTactics then d
      else #[]

    -- Helpers to check if two expressions are equal
    let checkExpr (sheetExpr subExpr : Expr) : IO ExerciseResultDebug := do
      -- Placeholder context and state
      let ctx : Core.Context := { fileName := "", fileMap := default }
      let cstate : Core.State := { env := sheet }

      -- Create a goal to prove that the two expressions are equal
      let helper : MetaM ExerciseResultDebug := do
        let eqExpr ← mkEq sheetExpr subExpr
        let mvar ← mkFreshExprMVar (some eqExpr)
        let mvarId := mvar.mvarId!
        -- Try refl
        try mvarId.refl;
            return { name := subName,
                     score := pts,
                     maxScore := pts,
                     status := "passed",
                     output := "Passed all tests",
                     sheet_name := name,
                     expected_status := "none",
                     output_log := "Proven equal by refl\n"
                            ++ s!"  Sheet: {constInfo.value!}\n"
                            ++ s!"  Submission: {subConstInfo.value!}" }
        catch _ => pure ()
        -- Try hrefl
        try mvarId.hrefl;
            return { name := subName,
                     score := pts,
                     maxScore := pts,
                     status := "passed",
                     output := "Passed all tests",
                     sheet_name := name,
                     expected_status := "none",
                     output_log := "Proven equal by hrefl\n"
                                    ++ s!"  Sheet: {constInfo.value!}\n"
                                    ++ s!"  Submission: {subConstInfo.value!}" }
        catch _ => pure ()
        -- Run tactics to prove equality
        -- TODO: check if there is backtracking after the tactic is applied
        for (tacName, tac) in tactics do
          let (_, goals) ← runTacticMAsMetaM (try tac catch _ => pure ()) [mvarId]
          if goals.isEmpty then
            return { name := subName,
                     score := pts,
                     maxScore := pts,
                     status := "passed",
                     output := "Passed all tests",
                     sheet_name := name,
                     expected_status := "none",
                     output_log := s!"Proven equal by {tacName}\n"
                                    ++ s!"  Sheet: {constInfo.value!}\n"
                                    ++ s!"  Submission: {subConstInfo.value!}" }
        return { name := subName,
                 score := 0.0,
                 maxScore := pts,
                 status := "failed",
                 output := "Not found to be equal"
                 sheet_name := name,
                 expected_status := "none",
                 output_log := "Not found to be equal\n"
                                ++ s!"  Sheet: {constInfo.value!}\n"
                                ++ s!"  Submission: {subConstInfo.value!}" }

      let (proved?, _, _ ) ← MetaM.toIO helper ctx cstate
      return proved?

    -- * Ensure declaration type matches sheet
    let checkType ← checkExpr constInfo.type subConstInfo.type
    if not (checkType.status == "passed") then
        pure { name := subName,
               score := 0.0
               maxScore := pts,
               status := "failed",
               output := "Type is different from expected: "
                          ++ s!"{constInfo.type} does not match "
                          ++ s!"{subConstInfo.type}",
               sheet_name := name,
               expected_status := "none",
               output_log := "Type is different from expected:\n"
                          ++ s!"  Sheet: {constInfo.value!}\n"
                          ++ s!"  Submission: {subConstInfo.value!}" }
    -- * Submitted declaration must match the soundness of the sheet decl
    else if (subConstInfo.isUnsafe && ! constInfo.isUnsafe) ||
            (subConstInfo.isPartial && ! constInfo.isPartial) then
      pure { name := subName,
             score := 0.0,
             maxScore := pts,
             status := "failed",
             output := "Declaration is partial or unsafe",
             sheet_name := name,
             expected_status := "none",
             output_log := "Declaration is partial or unsafe" }
    else if (!subConstInfo.hasValue) then
      pure { name := subName,
             score := 0.0,
             maxScore := pts,
             status := "failed",
             output := "Declaration does not contain a value",
             sheet_name := name,
             expected_status := "none",
             output_log := "Declaration does not contain a value" }
    else if (subConstInfo.value!.equal constInfo.value!) then
      pure { name := subName,
             maxScore := pts,
             score := pts,
             status := "passed",
             output := "Passed all tests",
             sheet_name := name,
             expected_status := "none",
             output_log := "Expr values are marked as equal" }
    else if (subConstInfo.value!.eqv constInfo.value!) then
      pure { name := subName,
             score := pts,
             maxScore := pts,
             status := "passed",
             output := "Passed all tests"
             sheet_name := name,
             expected_status := "none",
             output_log := "Expr values are marked as equivalent."
                            ++ s!"Sheet: {constInfo.value!}"
                            ++ s!"Submission: {subConstInfo.value!}" }
    else
      -- Run tactics to prove equality
      let sheetExpr := constInfo.value!
      let subExpr := subConstInfo.value!
      let result ← checkExpr sheetExpr subExpr
      pure result

def checkProof (name subName : Name) (pts : Float)
  (constInfo subConstInfo : ConstantInfo)
  (sheet submission : Environment) : IO ExerciseResultDebug := do
    -- Gather axioms in submitted declaration
    let (_, submissionState) :=
          ((CollectAxioms.collect name).run submission).run {}


    let validAxioms :=
      if let some t := validAxiomsAttr.getParam? sheet name then t
      else defaultValidAxioms

    -- Tests:
    -- * Ensure declaration doesn't use `sorry` (separate from other
    --   axioms since it's especially common)
    if subConstInfo.value?.any (·.hasSorry) then
      pure { name := subName,
             score := 0.0
             maxScore := pts,
             status := "failed",
             output := "Proof contains sorry",
             sheet_name := name,
             expected_status := "none",
             output_log := "Proof contains sorry" }
    -- * Ensure declaration type matches sheet
    else if not (constInfo.type == subConstInfo.type) then
      pure { name := subName,
             score := 0.0
             maxScore := pts,
             status := "failed",
             output := "Type is different from expected: "
                       ++ s!"{constInfo.type} does not match "
                       ++ s!"{subConstInfo.type}",
             sheet_name := name,
             expected_status := "none",
             output_log := "Type is different from expected: "
                        ++ s!"{constInfo.type} does not match "
                        ++ s!"{subConstInfo.type}" }
    -- * Submitted declaration must use only legal axioms

    else if let some badAx :=
      findInvalidAxiom submissionState.axioms.toList sheet submission validAxioms
    then
      pure { name := subName,
             score := 0.0,
             maxScore := pts,
             status := "failed",
             output := s!"Uses unexpected axiom {badAx}",
             sheet_name := name,
             expected_status := "none",
             output_log := s!"Uses unexpected axiom {badAx}" }
    -- * Submitted declaration must match the soundness of the sheet decl
    else if (subConstInfo.isUnsafe && ! constInfo.isUnsafe) ||
            (subConstInfo.isPartial && ! constInfo.isPartial) then
      pure { name := subName,
             score := 0.0
             maxScore := pts,
             status := "failed",
             output := "Declaration is partial or unsafe",
             sheet_name := name,
             expected_status := "none",
             output_log := "Declaration is partial or unsafe" }
    else
      pure { name := subName,
             score := pts,
             maxScore := pts,
             status := "passed",
             output := "Passed all tests"
             sheet_name := name,
             expected_status := "none"
             output_log := "Passed all tests" }

def gradeSubmission (sheet submission : Environment) : IO (Array ExerciseResult) := do
  let mut results := #[]
  for (name, constInfo) in sheet.constants.toList do
    -- Autograde proofs
    if let some pts := autogradedProofAttr.getParam? sheet name then
        if not name.isInternal then
          if let some subConstInfo := submission.find? name then
              let result ← checkProof name name pts constInfo subConstInfo sheet submission
              results := results.push result.toExerciseResult
            else
              let result :=
                { name,
                  score := 0.0
                  maxScore := pts,
                  status := "failed",
                  output := "Declaration not found in submission" }
              results := results.push result

    -- Autograde definitions
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        if let some subConstInfo := submission.find? name then
          let result ← checkDefinition name name pts constInfo subConstInfo sheet
          results := results.push result.toExerciseResult
        else
          let result :=
            { name,
              score := 0.0
              maxScore := pts,
              status := "failed",
              output := "Declaration not found in submission" }
          results := results.push result

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."
  return results

def testGradeSubmission (sheet submission : Environment) : IO (Array ExerciseResultDebug) := do
  let mut results := #[]
  for (name, constInfo) in sheet.constants.toList do
    -- Check autograding of proofs
    if let some pts := autogradedProofAttr.getParam? sheet name then
      if not name.isInternal then
        let mut currResults := #[]
        -- TODO: Could be optimized by precomputing the list of tests for each exercise
        -- and storing it in a map
        -- Check every submission constant that is labeled as a test for the current sheet constant
        for (subName, subConstInfo) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              let mut result ← checkProof name subName pts constInfo subConstInfo sheet submission
              result := { result with expected_status := expectedStatus }
              currResults := currResults.push result
        results := results ++ currResults

    -- Check autograding of definitions
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        let mut currResults := #[]
        -- Check every submission constant that is labeled as a test for the current sheet constant
        for (subName, subConstInfo) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              let mut result ← checkDefinition name subName pts constInfo subConstInfo sheet
              result := { result with expected_status := expectedStatus }
              currResults := currResults.push result
        results := results ++ currResults

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."

  return results
