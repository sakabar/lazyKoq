Require Import List.
Require Import Ascii String.


Module LazyKoq.
Variable stdin : string.

(* Exprの定義に困っていたが、Unlambdaに倣ってapplyを追加することで解決した *)
(* 小文字を使っているのは、名前を衝突させないため *)
Inductive Expr : Type :=
  | i : Expr
  | k : Expr
  | s : Expr
  | ap : Expr -> Expr -> Expr
.

(* e1を評価・簡約したらe2になる、という関係 *)
Inductive evalR : Expr -> Expr -> Prop :=
  | eval_I0 : evalR i i
  | eval_I1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (ap i x) xr
    
  | eval_K0 : evalR k k
  | eval_K1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (ap k x) (ap k xr)
  | eval_K2 : forall (x y xr :Expr),
    evalR x xr ->
    evalR (ap (ap k x) y) xr

  | eval_S0 : evalR s s
  | eval_S1 : forall (x xr:Expr),
    evalR x xr ->
    evalR (ap s x) (ap s xr)
  | eval_S2 : forall (x y xr yr:Expr),
    evalR x xr ->
    evalR y yr ->
    evalR (ap (ap s x) y) (ap (ap s xr) yr)
  | eval_S3 : forall (x y z xzr yzr res: Expr),
    evalR (ap x z) xzr ->
    evalR (ap y z) yzr ->
    evalR (ap xzr yzr) res ->
    evalR (ap (ap (ap s x) y) z) res
.

(* 前置演左子は使えない? *)
(* Locate "`". *)
(* Notation "'`' x y" := (ap x y) (at level 40). *)

Hypothesis I_eq: forall x:Expr, ap i x = x.
Hypothesis K_eq: forall x y:Expr, (ap (ap k x) y) = x.
Hypothesis S_eq: forall x y z:Expr, (ap (ap (ap s x) y) z) = (ap (ap x z) (ap y z)).

(* inner_evalを証明するために要請された *)
Lemma eval_I_res: forall(r:Expr), evalR i r <-> r = i.
Proof.
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_I0.
Qed.

(* eval_I_res と類似の補題 *)
Lemma eval_K_res: forall(r:Expr), evalR k r <-> r = k.
Proof.
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_K0.
Qed.

(* eval_I_res と類似の補題 *)
Lemma eval_S_res: forall(r:Expr), evalR s r <-> r = s.
Proof.
  intros r.
  split; intros H0; destruct r; try reflexivity; try inversion H0.
  apply eval_S0.
Qed.

Example testI: evalR (ap i i) i.
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

Theorem SKK: forall (e er:Expr), evalR e er -> evalR (ap (ap (ap s k) k) e) er.
Proof.
  intros e er H0.
  rewrite S_eq.
  rewrite K_eq.
  assumption.
Qed.

Definition zero := (ap k i).
Definition one := i.
Definition two := (ap (ap s (ap (ap s (ap k s)) k)) i).
Definition succ := (ap s (ap (ap s (ap k s)) k)).

Theorem succ_zero_is_one: forall f n:Expr,
  (ap (ap (ap succ zero) f) n) = (ap (ap one f) n).
Proof.
  unfold succ.
  unfold zero.
  unfold one.
  intros.
  rewrite I_eq.
  rewrite S_eq with (x := (ap (ap s (ap k s)) k)) (y := (ap k i)) (z := f).
  rewrite K_eq with (x := i) (y := f).
  rewrite S_eq with (x := (ap k s)).
  rewrite K_eq.
  rewrite S_eq.
  rewrite I_eq.
  rewrite K_eq.
  reflexivity.
Qed.

Lemma eval_appI_res: forall(e r:Expr), evalR e r -> evalR (ap i e) r.
Proof.
  intros e r H0.
  apply eval_I1.
  assumption.
Qed.

Lemma eval_appI_res_inv: forall(e r:Expr), evalR (ap i e) r -> evalR e r.
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
(*   | app i x => reduce x *)
(*   | i => i *)

(*   | (app (app k x) y) => (reduce x) *)
(*   | k => k *)
(*   | app k x => app k (reduce x) *)

(*   | (app (app (app s x) y) z) => (app (app (reduce x) (reduce z)) (app (reduce y) (reduce z))) *)
(*   | (app (app s x) y) => (app (app s (reduce x)) (reduce y)) *)
(*   | s => s *)

(*   | app e1 e2 => (app (reduce e1) (reduce e2)) *)
(*   end. *)

(* testZeroを証明するために要請された *)
Theorem inner_eval: forall (e1 e2 r1 res:Expr),
  evalR e1 r1 ->
  evalR (ap r1 e2) res ->
  evalR (ap e1 e2) res.
Proof.
  intros e1 e2 r1 res H0 H1.
  destruct e1.
  apply eval_I1.
  destruct e2.
  apply eval_I_res in H0.
  rewrite H0 in H1.
  apply eval_I_res.
  assert (evalR (ap i i) i).
  apply eval_I1.
  apply eval_I0.
Abort.

(* (標準入力の)文字列をバイト列に変換する *)
Fixpoint string_to_byte(s:string) : list nat :=
  match s with
  | EmptyString => 256 :: nil
  | String a s' => (nat_of_ascii a) :: string_to_byte s'
  end.

Fixpoint church_of_nat(n:nat) : Expr :=
  match n with
  | O => ap k i
  | S n' => ap succ (church_of_nat n')
  end.

Definition string_to_church_list(s:string) : list Expr :=
  map church_of_nat (string_to_byte s).

Eval compute in string_to_church_list "Hi".

Definition eCons(x y:Expr) : Expr := 
  ap (ap s (ap (ap s i) (ap k x))) (ap k y).

Fixpoint listExpr_to_Expr(l:list Expr) : Expr :=
  match l with
  | nil => church_of_nat 256
  | h :: t => eCons h (listExpr_to_Expr t)
  end.

End LazyKoq.
