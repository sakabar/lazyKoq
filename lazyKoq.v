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

  (* | rm_eval_I : forall (x res:Expr), *)
  (*   evalR (app I x) res -> *)
  (*   evalR x res *)

  (* | rm_eval_K : forall (x y res:Expr), *)
  (*   evalR (app (app K x) y) res -> *)
  (*   evalR x res *)

  (* | rm_eval_S : forall (x y z res:Expr), *)
  (*   evalR (app (app (app S x) y) z) res -> *)
  (*   evalR (app (app x z) (app y z)) res *)
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

Definition zero := (app K I).
Definition one := (app (app S (app (app S (app K S)) (app (app S (app K K)) I))) I).

(* inner_evalを証明するために要請された *)
Lemma eval_I_res: forall(r:Expr), evalR I r <-> r = I.
Proof.
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_I0.
Qed.

(* eval_I_res と類似の補題 *)
Lemma eval_K_res: forall(r:Expr), evalR K r <-> r = K.
Proof.
  Admitted.

(* eval_I_res と類似の補題 *)
Lemma eval_S_res: forall(r:Expr), evalR S r <-> r = S.
Proof.
  Admitted.

Lemma eval_appI_res: forall(e r:Expr), evalR e r -> evalR (app I e) r.
Proof.
  intros e r H0.
  apply eval_I1.
  assumption.
Qed.

Lemma eval_appI_res_inv: forall(e r:Expr), evalR (app I e) r -> evalR e r.
Proof.
  intros e r H0.
  induction e.
  apply eval_I_res.
  assert (evalR (app I I) I).
  apply eval_I1.
  apply eval_I0.
Abort.

(* inner_evalを証明するために要請された *)
(* 評価の結果は1通りである *)
Lemma eval_eq: forall(e1 e2 r1 r2:Expr),
  evalR e1 r1 -> evalR e2 r2 -> e1 = e2 -> r1 = r2.
Proof.
  intros e1 e2 r1 r2 H0 H1 H2.
  rewrite <- H2 in H1.
  destruct e1.
  apply eval_I_res in H0.
  apply eval_I_res in H1.
  rewrite H0.
  rewrite H1.
  reflexivity.

  apply eval_K_res in H0.
  apply eval_K_res in H1.
  rewrite H0.
  rewrite H1.
  reflexivity.

  apply eval_S_res in H0.
  apply eval_S_res in H1.
  rewrite H0.
  rewrite H1.
  reflexivity.

Abort.

(* testZeroを証明するために要請された *)
Theorem inner_eval: forall (e1 e2 r1 res:Expr),
  evalR e1 r1 ->
  evalR (app r1 e2) res ->
  evalR (app e1 e2) res.
Proof.
  intros e1 e2 r1 res H0 H1.
  destruct e1.
  apply eval_I1.
  destruct e2.
  apply eval_I_res in H0.
  rewrite H0 in H1.
  apply eval_I_res.
  assert (evalR (app I I) I).
  apply eval_I1.
  apply eval_I0.
Abort.

Example testZero : forall (s z res : Expr), evalR z res -> evalR (app (app zero s) z) res.
Proof.
  intros s z res H0.
  unfold zero.
  Abort.


Example testOne : forall(s z res:Expr), evalR (app s z) res -> evalR (app (app one s) z) res.
Proof.
  intros s z res H0.
  unfold one.
Abort.

End LazyKoq.
