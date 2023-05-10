import SoftwareFoundations

def main: IO Unit := do
  IO.println s!"Grader for \"Software Foundations\" in Lean {Lean.versionString}"
  IO.println (repr lf).pretty
