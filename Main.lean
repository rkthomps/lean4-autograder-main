import Lean
import AutograderLib
import Checking
-- Ensures Mathlib is compiled when the container is being uploaded:
-- import Mathlib
open Lean IO System Elab Command Meta Lean.Meta Lean.Elab.Tactic

def solutionDirName := "AutograderTests"

def resultsName := "lean-autograder-results.json"
def configName := "lean-autograder-config.json"

def compileAutograder : IO Unit := do
  -- Compile the autograder so we get all our deps, even if the sheet itself
  -- fails to compile
  let compileArgs : Process.SpawnArgs := {
    cmd := "/root/.elan/bin/lake"
    args := #["build", "autograder", solutionDirName]
  }
  let out ← IO.Process.output compileArgs
  if out.exitCode != 0 then
    IO.println <| "WARNING: The autograder failed to compile. Note that this "
      ++ "may not be an error if your assignment template contains errors. "
      ++ "Compilation errors are printed below:\n"
      ++ out.stderr


structure TestingPair where
  submission : String
  template : String
  deriving Repr

instance : FromJson TestingPair where
  fromJson? json := do
    let submission ← json.getObjVal? "submission"
    let template ← json.getObjVal? "template"
    let submissionStr ← submission.getStr?
    let templateStr ← template.getStr?
    return ⟨submissionStr, templateStr⟩


structure TestingConfig where
  pairs : List TestingPair

def x := Lean.FromJson

instance : FromJson TestingConfig where
  fromJson? json := do
    let pairsJson ← json.getArr?
    let pairs : Array TestingPair ← pairsJson.mapM (λ p => fromJson? p)
    return ⟨pairs.toList⟩


def getErrorsStr (ml : MessageLog) : IO String := do
  let errorMsgs := ml.toList.filter (λ m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => acc ++ "\n" ++ e) ""
  return errorTxt

def writeError {α} (errMsg : String) (instructorInfo: String := "")
  : IO α := do
  let result : FailureResult := {output := errMsg}
  IO.FS.writeFile resultsName (toJson result).pretty
  throw <| IO.userError (errMsg ++ "\n" ++ instructorInfo)

def readConfig : IO TestingConfig := do
  let configRaw ← IO.FS.readFile configName
  try
    let configJson ← IO.ofExcept <| Json.parse configRaw
    let config : TestingConfig ← IO.ofExcept <| fromJson? configJson
    return config
  catch _ =>
    exitWithError "" "Invalid JSON in autograder.json"


structure FileResult where
  file : String
  result : GradingResults
  deriving ToJson


structure TestSummary where
  name : String
  score : Float
  maxScore : Float
  deriving ToJson

structure FileSummary where
  file : String
  tests : Array TestSummary
  totalScore : Float
  totalMaxScore : Float
  deriving ToJson

structure Summary where
  files : Array FileSummary
  totalScore : Float
  totalMaxScore : Float
  deriving ToJson


def getSummary (results : Array FileResult) : Id Summary := do
  let mut totalScore := 0
  let mut totalMaxScore := 0
  let mut fileSummaries : Array FileSummary := #[]

  for f in results do
    let tests := f.result.tests
    let mut fileScore := 0
    let mut fileMaxScore := 0
    let mut testSummaries : Array TestSummary := #[]

    for t in tests do
      fileScore := fileScore + t.score
      fileMaxScore := fileMaxScore + t.maxScore
      testSummaries := testSummaries.push { name := t.name.toString, score := t.score, maxScore := t.maxScore }

    totalScore := totalScore + fileScore
    totalMaxScore := totalMaxScore + fileMaxScore
    fileSummaries := fileSummaries.push { file := f.file, tests := testSummaries, totalScore := fileScore, totalMaxScore := fileMaxScore }

  return { files := fileSummaries, totalScore := totalScore, totalMaxScore := totalMaxScore }


def printSummary (summary : Summary) : IO Unit := do
  for f in summary.files do
    IO.println s!"\n{f.file}: {f.totalScore} / {f.totalMaxScore}"
    for t in f.tests do
      IO.println s!"\t{t.name}: {t.score} / {t.maxScore}"

  IO.println s!"\nTotal: {summary.totalScore} / {summary.totalMaxScore}"




unsafe def main (_: List String) : IO Unit := do
  let cfg ← readConfig
  let output := ""

  let mut resultsArr : Array FileResult := #[]

  for filePair in cfg.pairs do
    let sheetContents ← IO.FS.readFile filePair.template
    let sheetCtx := Parser.mkInputContext sheetContents filePair.template
    let (sheetHeader, sheetParState, sheetMsgs) ← Parser.parseHeader sheetCtx
    enableInitializersExecution
    initSearchPath (← findSysroot)
    if sheetMsgs.hasErrors then
      exitWithError (instructorInfo := (← getErrorsStr sheetMsgs)) <|
        "There was an error processing the assignment template's imports. This "
          ++ "error is unexpected. Please notify your instructor and provide a "
          ++ "link to your submission."

    let (sheetHeadEnv, sheetMsgs)
      ← processHeader sheetHeader {} sheetMsgs sheetCtx


    if sheetMsgs.hasErrors then
      exitWithError (instructorInfo := (← getErrorsStr sheetMsgs)) <|
        "There was an error processing the assignment template's imports. This "
          ++ "error is unexpected. Please notify your instructor and provide a "
          ++ "link to your submission."

    let sheetCmdState : Command.State := Command.mkState sheetHeadEnv sheetMsgs {}
    let sheetFrontEndState
      ← IO.processCommands sheetCtx sheetParState sheetCmdState
    let sheet := sheetFrontEndState.commandState.env


    -- Grade the student submission
    -- Source: https://github.com/adamtopaz/lean_grader/blob/master/Main.lean
    let submissionContents ← IO.FS.readFile filePair.submission
    let inputCtx := Parser.mkInputContext submissionContents filePair.submission
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (headerEnv, messages) ← processHeader header {} messages inputCtx

    if messages.hasErrors then
      exitWithError <|
        "Your Lean file could not be processed because its header contains "
        ++ "errors. This is likely because you are attempting to import a module "
        ++ "that does not exist. A log of these errors is provided below; please "
        ++ "correct them and resubmit:\n\n"
        ++ (← getErrorsStr messages)

    let cmdState : Command.State := Command.mkState headerEnv messages {}
    let frontEndState ← IO.processCommands inputCtx parserState cmdState
    let messages := frontEndState.commandState.messages
    let submissionEnv := frontEndState.commandState.env

    let err ← getErrorsStr messages
    let output := output ++
      if messages.hasErrors
      then "Warning: Your submission contains one or more errors, which are "
            ++ "listed below. You should attempt to correct these errors prior "
            ++ "to your final submission. Any responses with errors will be "
            ++ "treated by the autograder as containing \"sorry.\"\n"
            ++ err
      else ""

    -- Provide debug info for staff
    IO.println "Submission compilation output:"
    let os ← messages.toList.mapM (λ m => m.toString)
    IO.println <| os.foldl (·++·) ""

    let tests : Array ExerciseResult ← gradeSubmission sheet submissionEnv
    let results : GradingResults := { tests, output }
    resultsArr := resultsArr.push { file := filePair.submission, result := results }

  let summary := Id.run <| getSummary resultsArr
  printSummary summary
  IO.FS.writeFile resultsName (toJson summary).pretty
