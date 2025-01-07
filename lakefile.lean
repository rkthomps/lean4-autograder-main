import Lake
open Lake DSL

package autograder where
  precompileModules := true

lean_lib AutograderTests where
  globs := #[.submodules `AutograderTests]

lean_lib AutograderLib

lean_lib Checking

@[default_target]
lean_exe autograder where
  root := `Main
  supportInterpreter := true
