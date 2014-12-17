module lambda

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Int
interpTy TyBool = Bool
interpTy (TyFun A T) = interpTy A -> interpTy T

using (G : Vect n Ty)
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop : HasType k G t -> HasType (FS k) (u :: G) t

  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : (x : Int) -> Expr G TyInt
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    Op : (interpTy a -> interpTy b -> interpTy c) -> Expr G a -> Expr G b -> Expr G c
    If : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a

  data Env : Vect n Ty -> Type where
    Nil : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)
