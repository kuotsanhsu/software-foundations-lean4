import SoftwareFoundations.LogicalFoundations
import BibTeX

/-- https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html#lab12 -/
def lf: Reference.Book where
  citekey  := "Pierce:SF1"
  author   := #[
    "Benjamin C. Pierce",
    "Arthur Azevedo de Amorim",
    "Chris Casinghino",
    "Marco Gaboardi",
    "Michael Greenberg",
    "Cătălin Hriţcu",
    "Vilhelm Sjöberg",
    "Brent Yorgey"]
  editor    := #["Benjamin C. Pierce"]
  title     := "Logical Foundations"
  series    := "Software Foundations"
  volume    := (1: PosInt)
  year      := (2022: Int)
  publisher := "Electronic textbook"
  note      := #["Version 6.2", "\\URL{http://softwarefoundations.cis.upenn.edu}"]
