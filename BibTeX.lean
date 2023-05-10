set_option autoImplicit false

/-- The type of positive integeres. Equivalent to `{ n: Nat // n > 0 }`. -/
structure PosInt where
  val: Nat
  pos: val ≠ 0 := by decide

instance (pred: Nat): OfNat PosInt pred.succ where
  ofNat := { val := pred.succ, pos := (nomatch .) }

inductive Month
  | January
  | February
  | March
  | April
  | May
  | June
  | July
  | August
  | September
  | October
  | November
  | December

/-!
# BibTeX

- [*The quick BibTeX guide*](https://www.bibtex.com/): a complete guide to BibTeX.
- [*A complete guide to the BibTeX format*](https://www.bibtex.com/g/bibtex-format/): a short guide to BibTeX formats.
-/
namespace Reference

/-- [Standard field types](https://www.bibtex.com/format/fields/). -/
structure StandardFields where
  /-- FIXME: must satisfy the regex `/[A-Za-z0-9\-_:]+/`. -/
  citekey: String
  /-- Address of the publisher or the institution. -/
  address: Option String := none
  /-- An annotation. -/
  annote: Option String := none
  /-- List of authors of the work. -/
  author: Array String
  /-- Title of the book. -/
  booktitle: Option String := none
  /-- Number of a chapter in a book. A book could have chapter 0, so there is no
  need to restrict `chapter` to be positive integers. -/
  chapter: Option Nat := none
  /-- Edition number of a book. FIXME: is the zeroth edition possible? -/
  edition: Option PosInt := none
  /-- List of editors of a book. -/
  editor: Option (Array String) := none
  /-- A publication notice for unusual publications. -/
  howpublished: Option String := none
  /-- Name of the institution that published and/or sponsored the report. -/
  institution: Option String := none
  /-- Name of the journal or magazine the article was published in. -/
  journal: Option String := none
  /-- The month during the work was published. -/
  month: Option Month := none
  /-- Notes about the reference. -/
  note: Option (Array String) := none
  /-- Number of the report or the issue number for a journal article. -/
  number: Option PosInt := none
  /-- Name of the institution that organized or sponsored the conference or that
  published the manual. -/
  organization: Option String := none
  /-- Page numbers or a page range. FIXME: roman numerals? -/
  pages: Option (Array Nat) := none
  /-- Name of the publisher. -/
  publisher: Option String := none
  /-- Name of the university or degree awarding institution. -/
  school: Option String := none
  /-- Name of the series or set of books. -/
  series: Option String := none
  /-- Title of the work. FIXME: mandatory? -/
  title: String
  /-- Type of the technical report or thesis. -/
  type: Option String := none
  /-- Volume number. -/
  volume: Option PosInt := none
  /-- Year the work was published. -/
  year: Option Int := none

/-
@book            {Pierce:SF1,
author       =   {Benjamin C. Pierce and
      Arthur Azevedo de Amorim and
      Chris Casinghino and
      Marco Gaboardi and
      Michael Greenberg and
      Cătălin Hriţcu and
      Vilhelm Sjöberg and
      Brent Yorgey},
editor       =   {Benjamin C. Pierce},
title        =   "Logical Foundations",
series       =   "Software Foundations",
volume       =   "1",
year         =   "2022",
publisher    =   "Electronic textbook",
note         =   {Version 6.2, \URL{http://softwarefoundations.cis.upenn.edu}}
}
-/

-- #check Lean.instReprRat
-- #check Lean.RBTree.instReprRBTree
open Std.Format in
instance: Repr StandardFields where
  reprPrec fields _ :=
    have pairs: Std.Format := s!"title = {fields.title.quote}"
    bracket "{" (s!"{fields.citekey}," ++ line ++ pairs) "}"


#check Array.instReprArray
structure Book extends StandardFields
instance: Repr Book where
  reprPrec book _ := "@book" ++ repr book.toStandardFields

/--
[*The 14 BibTeX entry types*](https://www.bibtex.com/e/entry-types/)
-/
inductive Entry
  | book (book: Book)

instance: Repr Entry where
  reprPrec
  | .book book, _ => repr book

instance: Coe Book Entry where coe := .book

/-- Test optional fields. -/
private def Knuth1997_minimal: Book where
  citekey := "Knuth1997"
  title := "The Art of Computer Programming"
  author := #["Knuth, Donal Ervin"]

#eval Knuth1997_minimal

/-- Example extracted from https://www.bibtex.com/g/bibtex-format/#bibtex-format-explained -/
private def Knuth1997: Entry := {
  Knuth1997_minimal with
  publisher := "Addison Wesley"
  address := "Boston, MA"
  edition := (3: PosInt)
  year := (1997: Int)
: Book}

#eval Knuth1997

end Reference
