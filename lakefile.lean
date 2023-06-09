import Lake
open Lake DSL

def leanArgs := #["-DautoImplicit=false"]

package «software-foundations» {
  moreServerArgs := leanArgs
  moreLeanArgs := leanArgs
}

lean_lib SoftwareFoundations
lean_lib BibTeX
lean_lib FormalLanguage
lean_lib Demo

@[default_target]
lean_exe grader {
  root := `Grader
}
