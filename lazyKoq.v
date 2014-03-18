Require Import Recdef.

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
  | eval_K1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (app K x) (app K xr)
  | eval_K2 : forall (x y xr :Expr),
    evalR x xr ->
    evalR (app (app K x) y) xr

  | eval_S0 : evalR S S
  | eval_S1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (app S x) (app S xr)
  | eval_S2 : forall (x y xr yr:Expr),
    evalR x xr ->
    evalR y yr ->
    evalR (app (app S x) y) (app (app S xr) yr)
  | eval_S3 : forall (x y z xzr yzr res: Expr),
    evalR (app x z) xzr ->
    evalR (app y z) yzr ->
    evalR (app xzr yzr) res ->
    evalR (app (app (app S x) y) z) res
.

(* 前置演左子は使えない? *)
(* Locate "`". *)
(* Notation "'`' x y" := (app x y) (at level 40). *)

Hypothesis I_eq: forall x:Expr, app I x = x.
Hypothesis K_eq: forall x y:Expr, (app (app K x) y) = x.
Hypothesis S_eq: forall x y z:Expr, (app (app (app S x) y) z) = (app (app x z) (app y z)).

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
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_K0.
Qed.

(* eval_I_res と類似の補題 *)
Lemma eval_S_res: forall(r:Expr), evalR S r <-> r = S.
Proof.
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_S0.
Qed.

Example testI: evalR (app I I) I.
Proof.
  apply eval_I1.
  apply eval_I0.
Qed.

(* SKKを証明するために要請された *)
(* 評価の結果はそれ以上簡約されない *)
(* この定理は成り立たない。反例は SII(SII) => SII(SII) *)
Theorem value_is_reduced: forall(e er:Expr), evalR e er -> evalR er er.
Proof.
Abort.

Theorem SKK: forall (e er:Expr), evalR e er -> evalR (app (app (app S K) K) e) er.
Proof.
  intros e er H0.
  rewrite S_eq.
  rewrite K_eq.
  assumption.
Qed.

Definition zero := (app K I).
Definition one := I.
Definition two := (app (app S (app (app S (app K S)) K)) I).
Definition succ := (app S (app (app S (app K S)) K)).

Theorem succ_zero_is_one: forall f n:Expr,
  (app (app (app succ zero) f) n) = (app (app one f) n).
Proof.
  unfold succ.
  unfold zero.
  unfold one.
  intros.
  rewrite I_eq.
  rewrite S_eq with (x := (app (app S (app K S)) K)) (y := (app K I)) (z := f).
  rewrite K_eq with (x := I) (y := f).
  rewrite S_eq with (x := (app K S)).
  rewrite K_eq.
  rewrite S_eq.
  rewrite I_eq.
  rewrite K_eq.
  reflexivity.
Qed.

Lemma eval_appI_res: forall(e r:Expr), evalR e r -> evalR (app I e) r.
Proof.
  intros e r H0.
  apply eval_I1.
  assumption.
Qed.

Lemma eval_appI_res_inv: forall(e r:Expr), evalR (app I e) r -> evalR e r.
Proof.
  intros.
  rewrite I_eq in H.
  assumption.
Qed.

(* inner_evalを証明するために要請された *)
(* 評価の結果は1通りである *)
(* これも、偽の命題である。反例は SII(SII)*)
Lemma eval_eq: forall(e r1 r2:Expr),
  evalR e r1 -> evalR e r2 -> r1 = r2.
Proof.
Abort.

(* 簡約、関数による表現 *)
(* 停止性を示せない *)
(* Function reduce(e:Expr) {measure app_length e}: Expr := *)
(*   match e with *)
(*   | app I x => reduce x *)
(*   | I => I *)

(*   | (app (app K x) y) => (reduce x) *)
(*   | K => K *)
(*   | app K x => app K (reduce x) *)

(*   | (app (app (app S x) y) z) => (app (app (reduce x) (reduce z)) (app (reduce y) (reduce z))) *)
(*   | (app (app S x) y) => (app (app S (reduce x)) (reduce y)) *)
(*   | S => S *)

(*   | app e1 e2 => (app (reduce e1) (reduce e2)) *)
(*   end. *)

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

End LazyKoq.
