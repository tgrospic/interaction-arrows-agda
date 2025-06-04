-- https://gist.github.com/tgrospic/29f0ce0cb63a2ead93aeaccbbf530800

data Grade' = A | B | C | D | E

data EssayS = Unassigned
            | Assigned
            | Writing
            | Reviewing
            | Done

data EssayCmd : Type -> EssayS -> EssayS -> Type where
  Assign   : EssayCmd () Unassigned Assigned
  Start    : EssayCmd () Assigned Writing
  Consult  : EssayCmd () state state
  Review   : EssayCmd () Writing Reviewing
  SendBack : EssayCmd () Reviewing Writing
  Grade    : Grade' -> EssayCmd Grade' Reviewing Done

  Pure     : ty -> EssayCmd ty state state
  (>>=)    : EssayCmd a state1 state2 -> (a -> EssayCmd b state2 state3) -> EssayCmd b state1 state3

essayProg1 : EssayCmd () Unassigned Assigned
essayProg1 = do
  Consult
  Consult
  Assign

essayProg2 : EssayCmd () Writing Writing
essayProg2 = do
  Review
  SendBack

essayProg3 : EssayCmd Grade' Reviewing Done
essayProg3 = SendBack >>= const Review >>= \_ => Grade C

essayTy : EssayCmd a s1 s2 -> Type
essayTy (Grade x) = (String, Int)
essayTy Consult   = ()
essayTy _         = String

r1 : essayTy Start
r1 = "Essay is started"

r2 : essayTy (Grade A)
r2 = ("Essay is done", 1)

r3 : essayTy Consult
r3 = ()
