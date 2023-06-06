#check Char.isWhitespace
#check Char.isLower
#check Char.isAlpha
#check Char.isDigit

inductive CharType | whitespace | alpha | digit | other

def classifyChar (c: Char): CharType :=
  if c.isWhitespace then .whitespace
  else if c.isAlpha then .alpha
  else if c.isDigit then .digit
  else .other
