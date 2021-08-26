module StmtRel 

import Data.Vect

import AST
import IR

data AExpBinOp : (e : Exp) -> (op : BOp) -> (f,g : Exp) -> Type where
    PlusBinOp : AExpBinOp (Plus f g) PLUS f g
    MinBinOp  : AExpBinOp (Min f g)  MINUS f g
    MulBinOp  : AExpBinOp (Mul f g)  MUL f g
    AndBinOp  : AExpBinOp (And f g)  AND f g 
    OrBinOp   : AExpBinOp (Or f g)   OR f g 
  
data ExpCndOp : (e : Exp) -> (op : COp) -> (f,g : Exp) -> Type where
    EqCndOp : ExpCndOp (Eq  f g) EQ f g
    GeCndOp : ExpCndOp (Gte f g) GE f g
    GtCndOp : ExpCndOp (Gt  f g) GT f g

data ExpTrans : (e : Exp) -> (ir : IRExp) -> Type where
    Num2   : ExpTrans (Num n) (CONST n)
    VarE2  : ExpTrans (VarE offset) (MEM offset)
    VarAE2 : ExpTrans (VarAE off pos) (MEM (off+pos))
    BinOp2 : AExpBinOp e op f g 
         -> ExpTrans f f_ir
         -> ExpTrans g g_ir
         -> ExpTrans e (BINOP op f_ir g_ir)
    CJump2 : ExpCndOp e op f g 
         -> ExpTrans f f_ir
         -> ExpTrans g g_ir 
         -> (l1 : Nat)
         -> (l2 : Nat)
         -> ExpTrans e (CJUMP op f_ir g_ir l1 l2) 

data ArrayDecToIR : (index : Nat) -> (sizeRemaining : Nat) -> (ir : IRStmt) -> Type where
    ArrayNop  : ArrayDecToIR index Z NOP
    ArrayCons : ArrayDecToIR (S index) n tl 
            ->  ArrayDecToIR index (S n) (SEQ (MOVE (MEM (index)) (CONST Z)) tl) 

data StmDataTrans : Stm -> IRStmt -> Type where
    VarDecRel : StmDataTrans (VarDeclare offset value) (MOVE (MEM offset) (CONST value))
    ArrDecRel :  ArrayDecToIR offset (S size) ir
              -> StmDataTrans (ArrayDeclare offset (S size)) ir
    AssignRelVar :  ExpTrans e2 e2'
                 -> StmDataTrans (Assign (VarE offset) e2) (MOVE (MEM offset) e2')
    AssignRelArr :  ExpTrans e2 e2'
                 -> StmDataTrans (Assign (VarAE offset position) e2) (MOVE (MEM (offset+position)) e2') 
                 
data StmControlTrans : Vect n Stm -> IRStmt -> Type where
    NopIt : StmControlTrans [] NOP
    IfRel : (l1,l2,l3 : Nat)
        ->  ExpTrans e e'
        ->  StmControlTrans s1 stms1'
        ->  StmControlTrans s2 stms2'
        ->  StmControlTrans ss tl
        ->  StmControlTrans ((If e1 s1 s2)::ss) (SEQ (SEQ (SEQ (EXP e') 
                                                     (SEQ (SEQ (LABEL l1) (SEQ stms1' (JUMP l3)))
                                                          (SEQ (LABEL l2) stms2'))
                                                     )
                                                     (LABEL l3)) tl)

data StmTrans : Stm -> IRStmt -> Type where
    DataStm : StmDataTrans s ir -> StmTrans s ir 
    ContStm : StmControlTrans [s] ir -> StmTrans s ir 

translateExp : (u : Unique)
            -> (e : Exp) 
            -> (Unique, (ir : IRExp ** ExpTrans e ir))
translateExp u (Num n) =  (u, (CONST n ** Num2))
translateExp u (VarE offset) = 
   (u, (MEM offset ** VarE2))
translateExp u (VarAE offset position) =
   (u, (MEM (offset + position) ** VarAE2))
translateExp u (Plus e1 e2) =
      case translateExp u e1 of
        (u1, (x ** e1')) => case translateExp u1 e2 of 
                                (u2, (y ** e2')) => (u2, (BINOP PLUS x y ** BinOp2 PlusBinOp e1' e2'))
translateExp u (Min e1 e2) =
  case translateExp u e1 of
    (u1, (x ** e1')) => case translateExp u1 e2 of 
                                  (u2, (y ** e2')) => (u2, (BINOP MINUS x y ** BinOp2 MinBinOp e1' e2'))       
translateExp u (Mul e1 e2) =
  case translateExp u e1 of
    (u1, (x ** e1')) => case translateExp u1 e2 of 
                          (u2, (y ** e2')) => (u2, (BINOP MUL x y ** BinOp2 MulBinOp e1' e2'))
translateExp u (And e1 e2) =
  case translateExp u e1 of
    (u1, (x ** e1')) => case translateExp u1 e2 of 
                              (u2, (y ** e2')) => (u2, (BINOP AND x y ** BinOp2 AndBinOp e1' e2'))
translateExp u (Or e1 e2) =     
  case translateExp u e1 of
    (u1, (x ** e1')) => case translateExp u1 e2 of 
                              (u2, (y ** e2')) => (u2, (BINOP OR x y ** BinOp2 OrBinOp e1' e2'))
translateExp u (Eq e1 e2) =
  case translateExp u e1 of 
    (u1, (x ** e1')) => case translateExp u1 e2 of
                              (u2, (y ** e2')) => (u2+3, (CJUMP EQ x y (u+1) (u2+2) ** CJump2 EqCndOp e1' e2' (u+1) (u2+2)))

translateExp u (Gt e1 e2) =
  case translateExp u e1 of 
    (u1, (x ** e1')) => case translateExp u1 e2 of
                               (u2, (y ** e2')) => (u2+3, (CJUMP GT x y (u+1) (u2+2) ** CJump2 GtCndOp e1' e2' (u+1) (u2+2)))
translateExp u (Gte e1 e2) =
  case translateExp u e1 of 
    (u1, (x ** e1')) => case translateExp u1 e2 of
                                (u2, (y ** e2')) => (u2+3, (CJUMP GE x y (u+1) (u2+2) ** CJump2 GeCndOp e1' e2' (u+1) (u2+2))) 


translateDataStmt : (l : Unique)
                 -> (s : Stm)
                 -> Maybe (ir : IRStmt ** StmDataTrans s ir)
translateDataStmt l (VarDeclare offset value) =
    Just ( (MOVE (MEM offset) (CONST value)) ** VarDecRel)
translateDataStmt l s = ?hole99

translateControlStmt :  (l : Unique)
                     -> (ss : Vect n Stm)
                     -> Maybe (ir : IRStmt ** StmControlTrans ss ir)
translateControlStmt l [] = Just (NOP ** NopIt )
translateControlStmt l ((If e1 s1 s2)::ss) =
    case translateExp l e1 of
        (l1, (e1' ** pe1)) => 
            case translateControlStmt l1 s1 of
                Nothing => Nothing
                Just (s1' ** ps1) => 
                    case translateControlStmt l1 s2 of 
                        Nothing => Nothing
                        Just (s2' ** ps2) => 
                            case translateControlStmt l1 ss of
                                Nothing => Nothing
                                Just (ss' ** pss) =>
                                   Just ( (SEQ (SEQ (SEQ (EXP e1') 
                                               (SEQ (SEQ (LABEL l) (SEQ s1' (JUMP l1)))
                                                    (SEQ (LABEL l1) s2'))
                                          )
                                          (LABEL l1)) ss') ** IfRel l l1 l1 pe1 ps1 ps2 pss  )

translateStmt : (l : Unique)
             -> (s : Stm)
             -> Maybe (ir : IRStmt ** StmTrans s ir) 
translateStmt l (VarDeclare offset value) =
    case translateDataStmt l (VarDeclare offset value) of
        Nothing => Nothing
        Just (ir ** pir) => Just (ir ** DataStm pir)
translateStmt l (If e1 s1 s2) = 
    case translateControlStmt l [If e1 s1 s2] of
        Nothing => Nothing 
        Just (ir ** pir) => Just (ir ** ContStm pir)

translateStmt l s = ?hole