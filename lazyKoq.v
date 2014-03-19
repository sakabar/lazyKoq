Require Import List.
Require Import EqNat.
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
Variables F N : Expr.

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
Definition pred := ap (ap s (ap (ap s (ap k s)) (ap (ap s (ap k (ap s (ap k s)))) (ap (ap s (ap k (ap s (ap k (ap (ap s s)(ap k k)))))) (ap (ap s (ap k (ap s (ap k k)))) (ap (ap s (ap (ap s (ap k s)) k)) (ap k (ap (ap s (ap k (ap s (ap k (ap s i))))) (ap (ap s (ap k (ap s (ap k k)))) (ap (ap s (ap k (ap s i))) k)))))))))) (ap k (ap k (ap k i))).

Theorem succ_zero_is_one: forall f n:Expr,
  (ap (ap (ap succ zero) f) n) = (ap (ap one f) n).
Proof.
  unfold succ.
  unfold zero.
  unfold one.
  intros.
  rewrite I_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite S_eq.
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
(* ステップ数を制限して停止性を示す *)
Fixpoint reduce(e:Expr)(step:nat) : Expr :=
  match step with
  | O => e
  | S step' =>
    match e with
    | ap i x => reduce x step'
    | i => i

    | (ap (ap k x) y) => (reduce x step')
    | k => k
    | ap k x => ap k (reduce x step')

    | (ap (ap (ap s x) y) z) => (ap (ap (reduce x step') (reduce z step')) (ap (reduce y step') (reduce z step')))
    | (ap (ap s x) y) => (ap (ap s (reduce x step')) (reduce y step'))
    | s => s

    | ap e1 e2 => reduce (ap (reduce e1 step') (reduce e2 step')) step'
    end
  end.

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

Definition eCons(x y:Expr) : Expr := 
  ap (ap s (ap (ap s i) (ap k x))) (ap k y).
Definition eHead(lst:Expr) := ap lst k.
Definition eTail(lst:Expr) := ap lst (ap k i).

Fixpoint listExpr_to_Expr(l:list Expr) : Expr :=
  match l with
  | nil => church_of_nat 256
  | h :: t => eCons h (listExpr_to_Expr t)
  end.

Definition lst_zero_one := eCons zero one.
Example head_lst_zero_one: eHead lst_zero_one = zero.
Proof.
  unfold eHead.
  unfold lst_zero_one.
  unfold zero.
  unfold one.
  unfold eCons.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite I_eq.
  rewrite K_eq.
  reflexivity.
Qed.

Example tail_lst_zero_one: eTail lst_zero_one = one.
Proof.
  unfold eTail.
  unfold lst_zero_one.
  unfold zero.
  unfold one.
  unfold eCons.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite I_eq.
  rewrite K_eq.
  rewrite I_eq.
  reflexivity.
Qed.

Theorem eCons_eHead: forall(x y:Expr),
  eHead (eCons x y) = x.
Proof.
  intros x y.
  unfold eHead.
  unfold eCons.
  rewrite S_eq.
  rewrite S_eq.
  rewrite I_eq.
  rewrite K_eq.
  rewrite K_eq.
  reflexivity.
Qed.

Theorem eCons_eTail: forall(x y:Expr),
  eTail (eCons x y) = y.
Proof.
  intros x y.
  unfold eCons.
  unfold eTail.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite I_eq.
  rewrite K_eq.
  rewrite I_eq.
  reflexivity.
Qed.

Fixpoint church_num_to_nat(e:Expr) : nat := 256.
  (* match e with *)
  (* | ap k i => 0 *)
  (* | _ => 1 + church_num_to_nat (reduce (ap pred e) 1) *)
  (* end. *)

Goal forall n f:Expr,
  ap (ap (reduce (ap succ zero) 1) f) n = ap f n.
Proof.
  intros n f.
  unfold succ.
  unfold zero.
  unfold reduce.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite I_eq.
  reflexivity.
Qed.

Example church_num_to_nat_0: church_num_to_nat zero = 0.
Proof.
Abort.

Example pred_one_is_zero: ap (ap (ap pred one) F) N = N.
Proof.
  unfold pred.
  unfold one.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite I_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite S_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite K_eq.
  rewrite S_eq.
  rewrite I_eq.
  rewrite I_eq.
  rewrite I_eq.
  rewrite K_eq.
  rewrite K_eq.
  reflexivity.
Qed.

Fixpoint church_stream_to_string(lst:Expr)(step:nat): string :=
  match step with
  | O => EmptyString
  | S step' => if beq_nat (church_num_to_nat (eHead lst)) 256 then EmptyString else String (ascii_of_nat (church_num_to_nat (eHead lst))) (church_stream_to_string (eTail lst) step')
  end.

End LazyKoq.
