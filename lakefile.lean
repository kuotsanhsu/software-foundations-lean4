import Lake
open Lake DSL

package «software-foundations»

lean_lib SoftwareFoundations
lean_lib BibTeX

@[default_target]
lean_exe grader {
  root := `Grader
}
