module Main

import Data.Vect

import Utils
import Utils.Ord

import AST
import IR

%default total
%access public export



data ElemToNat : (elem : Elem x xs) -> (n : Nat) -> Type where
  Here  : ElemToNat Here Z
  There : ElemToNat later k -> ElemToNat (There later) (S k)

elemToNat : (elem : Elem x xs) -> Subset Nat (ElemToNat elem)
elemToNat Here = Element Z Here
elemToNat (There later) with (elemToNat later)
  | Element k prf = Element (S k) (There prf)

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

data AExpToIRExp : (env : Env) -> (e : Exp) -> (ir : IRExp) -> Type where
  Num   : AExpToIRExp env (Num n) (CONST n)
  VarE  : (inEnv  : Elem x env)
       -> (memloc : ElemToNat inEnv ptr)
       -> AExpToIRExp env (VarE x) (MEM ptr)
  VarAE : (inEnv  : Elem x env)
       -> (memloc : ElemToNat inEnv ptr)
       -> AExpToIRExp env (VarAE xs off) (MEM (ptr + off))
  BinOp : AExpBinOp e op f g 
       -> AExpToIRExp env f f_ir
       -> AExpToIRExp env g g_ir
       -> AExpToIRExp env e (BINOP op f_ir g_ir)
  CJump : ExpCndOp e op f g 
       -> AExpToIRExp env f f_ir
       -> AExpToIRExp env g g_ir 
       -> (l1 : Nat)
       -> (l2 : Nat)
       -> AExpToIRExp env e (CJUMP op f_ir g_ir l1 l2) 

data AExpToIRExp2 : (e : Exp) -> (ir : IRExp) -> Type where
        Num2   : AExpToIRExp2 (Num n) (CONST n)
        VarE2  : AExpToIRExp2 (VarE offset) (MEM offset)
        VarAE2 : AExpToIRExp2 (VarAE off pos) (MEM (off+pos))
        BinOp2 : AExpBinOp e op f g 
             -> AExpToIRExp2 f f_ir
             -> AExpToIRExp2 g g_ir
             -> AExpToIRExp2 e (BINOP op f_ir g_ir)
        CJump2 : ExpCndOp e op f g 
             -> AExpToIRExp2 f f_ir
             -> AExpToIRExp2 g g_ir 
             -> (l1 : Nat)
             -> (l2 : Nat)
             -> AExpToIRExp2 e (CJUMP op f_ir g_ir l1 l2) 

data StmtToIRMoveSeq : Nat -> Nat -> IRStmt -> Type where
  Nil  : StmtToIRMoveSeq fp Z NOP
  Cons : StmtToIRMoveSeq (S fp) len tl
      -> StmtToIRMoveSeq fp (S len) (SEQ (MOVE (MEM fp) (CONST Z)) tl)

data StmtToIRStmt : Stm -> IRStmt -> Type where
  Var  : (fp : Nat) -> StmtToIRStmt (Var x n) (MOVE (MEM fp) (CONST n))
  VarA : (fp : Nat) -> StmtToIRMoveSeq fp len seq -> StmtToIRStmt (VarA xs len) seq
  AssV : (fp : Nat) -> StmtToIRStmt (Assign e1 e2) (MOVE (MEM  fp)  exp') 


data StmtKind : Type where
  Vector : StmtKind
  Scalar : StmtKind

Arrs : StmtKind -> Nat -> Type 
Arrs Vector a = (Vect a Stm, Nat)
Arrs Scalar a = Stm 

data GetOffset : IRStmt -> Nat -> Nat -> Type where
  Var3  : GetOffset (MOVE (MEM offset) (CONST n)) offset (S offset)
 -- VarA3 : GetOffset (VarA2 offset size) offset (offset+size) 

data StmtKindtoStmt : (vectLength : Nat) -> (n : StmtKind) -> Arrs n a ->  IRStmt -> Type where
  Var2  : (offset : Nat) -> StmtKindtoStmt Z Scalar (Var x n) (MOVE (MEM offset) (CONST n))
  VarA2 : (offset : Nat) -> (size : Nat) -> StmtToIRMoveSeq offset size seq -> StmtKindtoStmt Z Scalar (VarA xs size) seq
  NopIt : StmtKindtoStmt Z Vector ([],offset) NOP
  SeqIt : (a : StmtKindtoStmt Z Scalar x y)
       -> GetOffset y offset offset2
       -> StmtKindtoStmt n Vector (xs, offset2) ys 
       -> StmtKindtoStmt (S n) Vector ((x::xs), offset) (SEQ y ys)
  If2   : AExpToIRExp2 e e'
       -> StmtKindtoStmt n Vector (s1, offset) stmts1'
       -> GetOffset stmts1' offset offset1
       -> StmtKindtoStmt m Vector (s2, offset1) stmts2'
       -> StmtKindtoStmt Z Scalar (If e1 s1 s2) (SEQ (SEQ (EXP e') 
                                                     (SEQ (SEQ (LABEL l1) (SEQ stms1' (JUMP l3)))
                                                          (SEQ (LABEL l2) stms2'))
                                                     )
                                                     (LABEL l3)   
                                                )
AssV2 :  (offset : Nat)
      -> AExpToIRExp2 e2 exp' 
      -> StmtKindtoStmt Z Scalar (Assign e1 e2) (MOVE (MEM offset)  exp')

allocate :  (fp : FP)
         -> Nat 
         -> IRStmt
         -> IRStmt
allocate fp Z s = s
allocate fp (S n) s = allocate (fp+1) n (SEQ s ((MOVE (MEM fp) (CONST 0))))

allocate2 : (fp : FP) -> (l : Nat) -> (s : IRStmt ** StmtToIRMoveSeq fp l s)
allocate2 fp Z = (NOP ** Nil)
allocate2 fp (S n) = case allocate2 (S fp) n of 
                      (s' ** ms) => ((SEQ (MOVE (MEM fp) (CONST Z)) s') **  Cons ms)

Arr : (s : Stm) -> (n : Nat) -> Nat
Arr (Var _ _) n = S n
Arr (VarA _ size) n = n + size
Arr (Assign _ _) n = n
Arr _ n = n

translateExp : (u : Unique)
            -> (e : Exp) 
            -> (Unique, (ir : IRExp ** AExpToIRExp2 e ir))
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

lookupN : (fp : FP) -> (e : Env) -> (name : Nat) -> Maybe FP
lookupN fp [] name = Nothing
lookupN fp (n::names) name = 
  case decEq n name of
    No c => lookupN (fp+1) names name
    Yes Refl => Just fp  

translateStmt : (vectLength : Nat)
             -> (n : StmtKind)
             -> (u : Unique)
             -> (s : Arrs n vectLength)
             -> Maybe (ir : IRStmt ** StmtKindtoStmt vectLength n s ir)
translateStmt Z Scalar u (Assign (VarE offset) exp) = 
  case translateExp u exp of
    (u1, (exp2 ** t)) => Just (MOVE (MEM  offset) exp2 ** AssV2 offset t)
translateStmt Z Scalar u (Assign (VarAE offset position) exp) = 
  case translateExp u exp of
    (u1, (exp2 ** t)) => Just (MOVE (MEM  (offset+position)) exp2 ** AssV2 (offset+position) t)
translateStmt Z Scalar u (VarA offset size) =
  case allocate2 offset size of 
    (s1 ** sm) => Just (s1 ** VarA2 offset size sm)
translateStmt Z Scalar u (Var offset init) = 
  Just ((MOVE (MEM offset) (CONST init)) ** Var2 offset) 
-- translateStmt Z Scalar u (If {n} {m} e s1 s2) = 
--     case translateExp u e of 
--       (u1, (e' ** te)) => case translateStmt n Vector u1 s1 of
--                              Just (s1' ** ts1) => case translateStmt m Vector u1 s2 of 
--                                                      Just (s2' ** ts2) => Just  (SEQ (SEQ (EXP e') 
--                                                                                     (SEQ (SEQ (LABEL u1) (SEQ s1' (JUMP (u1+3) )))
--                                                                                          (SEQ (LABEL (u1+2) ) s2'))
--                                                                                     )
--                                                                                     (LABEL (u1+3))   
--     
--                                                                              ** If2 te ts1 Var3 ts2)
translateStmt Z Vector u ([], Z) = Just (NOP ** NopIt)
translateStmt (S n) Vector u ((s :: ss), startOffset) = 
 case translateStmt Z Scalar u s of 
              Nothing => Nothing
              Just (s' ** ts) => case translateStmt n Vector u (ss, ?) of 
                                  Nothing => Nothing
                                  Just (ss' ** tss) => Just (SEQ s' ss' **  SeqIt ts Var3 tss)
    
-- SeqIt : (a : StmtKindtoStmt Z Scalar x y)
--        -> GetOffset y offset offset2
--        -> StmtKindtoStmt n Vector (xs, offset2) ys 
--        -> StmtKindtoStmt (S n) Vector ((x::xs), offset) (SEQ y ys)

  -- AExpToIRExp2 e e'
  -- -> StmtKindtoStmt n Vector (s1, offset) stmts1'
  -- -> GetOffset stmts1' offset offset1
  -- -> StmtKindtoStmt m Vector (s2, offset1) stmts2'
  -- -> StmtKindtoStmt Z Scalar (If e1 s1 s2) (SEQ (SEQ (EXP e') 
  --                                               (SEQ (SEQ (LABEL l1) (SEQ stms1' (JUMP l3)))
  --                                                    (SEQ (LABEL l2) stms2'))
  --                                               )
  --                                               (LABEL l3)   
  --                                          )  
translateStmt _ _ _ _ = ?hole

{- translateStmt u fp env (If e s1 s2) =
  case translateExp u env e of 
    Nothing => Nothing
    Just (u2, (e2 ** t)) => case translateStmt u2 fp env s1 of 
                              Nothing => Nothing 
                              Just (env2, (s1' ** t2)) => case translateStmt u2 fp env2 s2 of
                                                            Nothing => Nothing 
                              Just thing => ?hole -}
-- translateStmt u fp env s = ?holeHere44 

-- translateStmts : (u : Unique)
--               -> (fp : FP)
--               -> (env : Env {n=n})
--               -> (s :  Vect m Stm)
--               -> Maybe (Env {n = Arr s n}, (ir : IRStmt ** StmtToIRStmt s ir))

-- Labels need to be unique


  -- CndOp : (eRop   : ExpCndOp e op)
  --      -> (tt,ff  : Nat)
  --      -> (ttLTff : LTNat tt ff)
  --      -> ExpToIRExp env e e_ir
  --      -> ExpToIRExp env f f_ir
  --      -> ExpToIRExp env e (CJUMP op e_ir f_ir (show tt) (show ff))

{-
data StmtToIRMoveSeq : Nat -> Nat -> IRStmt -> Type where
  Nil  : StmtToIRMoveSeq fp Z NOP
  Cons : StmtToIRMoveSeq (S fp) len tl
      -> StmtToIRMoveSeq fp (S len) (SEQ (MOVE (MEM fp) (CONST Z)) tl)

data StmtToIRStmt : Stm -> IRStmt -> Type where
  Var  : (fp : Nat) -> StmtToIRStmt (Var x n) (MOVE (MEM fp) (CONST n))
  VarA : (fp : Nat) -> StmtToIRMoveSeq fp len seq -> StmtToIRStmt (VarA xs len) seq
  |||
  ||| cond
  ||| label_tt
  ||| stmts_tt
  ||| jump_end
  ||| label_ff
  ||| stmts_ff
  ||| label_end
  ||| stmts_tl
  |||
  ||| Do all labels need to be unique, or can we get away with localised instances?
  If   : ExpToIRExp env e e_ir
      -- -> IsCond e_ir 
      -> StmtToIRStmt (If e tt ff) (e_ir ++ (LABEL (show l_tt)) ++ tt_ir ++ (JUMP end) ++
                                    (LABEL (show l_ff)) ++ ff_ir ++ (LABEL (show l_end)))
-}

main : IO ()
main = putStrLn ""
