Module LazyKoq.
(* Variable Input : Expr. *)

(* Exprの定義に困っていたが、Unlambdaに倣ってapplyを追加することで解決した *)
Inductive Expr : Type :=
  | I : Expr
  | K : Expr
  | S : Expr
  | app : Expr -> Expr -> Expr
.

(* e1を評価・簡約したらe2になる、という関係 *)
Inductive evalR : Expr -> Expr -> Prop :=
  | eval_I0 : evalR I I
  | eval_I1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (app I x) xr

  | eval_K0 : evalR K K
  | eval_K1 : forall (x:Expr),
    evalR (app K x) (app K x)
  | eval_K2 : forall (x y xr :Expr),
    evalR x xr ->
    evalR (app (app K x) y) xr

  | eval_S0 : evalR S S
  | eval_S1 : forall (x:Expr),
    evalR (app S x) (app S x)
  | eval_S2 : forall (x y:Expr),
    evalR (app (app S x) y) (app (app S x) y)
  | eval_S3 : forall (x y z xzr yzr res: Expr),
    evalR (app x z) xzr ->
    evalR (app y z) yzr ->
    evalR (app xzr yzr) res ->
    evalR (app (app (app S x) y) z) res
.
(* 前置演左子は使えない? *)
(* Locate "`". *)
(* Notation "'`' x y" := (app x y) (at level 40). *)

Example testI: evalR (app I I) I.
Proof.
  apply eval_I1.
  apply eval_I0.
Qed.

Theorem SKK: forall (e er:Expr), evalR e er -> evalR (app (app (app S K) K) e) er.
Proof.
  intros e er H0.
  apply eval_S3 with (xzr := (app K e)) (yzr := (app K e)).
  apply eval_K1.
  apply eval_K1.
  apply eval_K2.
  assumption.
Qed.

End LazyKoq.
