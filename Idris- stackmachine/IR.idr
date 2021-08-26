module IR

import Instruction

-- %default total
%access public export

data COp : Type where
  EQ : COp
  NE : COp
  LT : COp
  GT : COp
  LE : COp
  GE : COp

data BOp : Type where
  PLUS  : BOp
  MINUS : BOp
  MUL   : BOp
  AND   : BOp
  OR    : BOp

data IRExp : Type where
  CONST : Nat -> IRExp
  BINOP : BOp -> IRExp -> IRExp -> IRExp
  MEM   : Nat -> IRExp
  CJUMP : COp -> IRExp -> IRExp -> Nat -> Nat -> IRExp

data IRStmt : Type where
  MOVE  : IRExp  -> IRExp -> IRStmt
  EXP   : IRExp  -> IRStmt
  JUMP  : Nat -> IRStmt
  SEQ   : IRStmt -> IRStmt -> IRStmt
  LABEL : Nat -> IRStmt
  NOP   : IRStmt

{-
(++) : IRStmt -> IRStmt -> IRStmt
(++) (MOVE e f) s = (SEQ (MOVE e f) s)
(++) (EXP e) s = (SEQ (EXP e) s)
(++) (JUMP l) s = (SEQ (JUMP l) s)
(++) (LABEL l) s = (SEQ (LABEL l) s)
(++) (SEQ r s) t = SEQ r (s ++ t)
(++) NOP s = s
-}

codeGenE : IRExp -> List Instruction
codeGenE (CONST i) = [PUSH i]
codeGenE (MEM fp)  = [LOAD fp]
codeGenE (BINOP PLUS e1 e2) = 
  let e1' = codeGenE e1
      e2' = codeGenE e2
  in e1' ++ e2' ++ [ADD]
codeGenE (BINOP MINUS e1 e2) = 
  let e1' = codeGenE e1
      e2' = codeGenE e2
  in e1' ++ e2' ++ [SUB]
codeGenE (CJUMP EQ e1 e2 t f) =
  let e1' = codeGenE e1
      e2' = codeGenE e2
  in e1' ++ e2' ++ [ISEQ, NOT, JIF f] 
codeGenE (CJUMP GE e1 e2 t f) =
  let e1' = codeGenE e1
      e2' = codeGenE e2
  in e1' ++ e2' ++ [ISGE, NOT, JIF f]  
codeGenE (CJUMP GT e1 e2 t f) =
  let e1' = codeGenE e1
      e2' = codeGenE e2
  in e1' ++ e2' ++ [ISGT, NOT, JIF f]   

codeGenS : IRStmt -> List Instruction
codeGenS (SEQ s1 s2) = codeGenS s1 ++ codeGenS s2
codeGenS (LABEL name) = [Instruction.LABEL name]
codeGenS (JUMP name) = [Instruction.JMP name]
codeGenS (MOVE (MEM addr) e2) 
  = let e2' = codeGenE e2 in e2' ++ [Instruction.STORE addr]
codeGenS (EXP e1) = 
  let e1' = codeGenE e1
  in e1'
codeGenS (NOP) = []


