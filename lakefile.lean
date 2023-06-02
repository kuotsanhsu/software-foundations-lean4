import Lake
open Lake DSL

def leanArgs := #["-DautoImplicit=false"]

package «software-foundations» {
  moreServerArgs := leanArgs
  moreLeanArgs := leanArgs
}

@[default_target]
lean_lib SoftwareFoundations
@[default_target]
lean_lib BibTeX

@[default_target]
lean_exe grader {
  root := `Grader
}
