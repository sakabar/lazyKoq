Require Import List.
Require Import EqNat.
Require Import Ascii String.
Require Import ZArith.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.

Module Lz.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).


Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(* ラムダ式 *)
Inductive expr : Type :=
  | V : nat -> expr
  | L : expr -> expr
  | A : expr -> expr -> expr
.

(* Section Sec. *)
  (* Hypothesis I_eq: forall (x:expr), A (L (V 0)) x = x. *)
  (* Hypothesis K_eq: forall (x y:expr), A (A (L (L (V 1))) x) y = x. *)
  (* Hypothesis S_eq: forall (x y z:Expr), *)
  (*   (A (A (A (L (L (L (A (A (V 2) (V 0)) (A (V 1) (V 0)))))) x) y) z) = (). *)

Open Scope string_scope.

(* TODO *)
Definition string_of_nat(n:nat) : string :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => ""
  end.

(* TODO: *)
(* nat -> 桁数 *)
(* nat -> 桁ごとのリスト *)
(* 桁ごとのリスト -> string *)

(* 型が合わないので定義できていない *)
(* Function getDigitList(z:Z) {measure z}: list Z := *)
(*   match Zcompare z 10 with *)
(*   | Gt => [z] *)
(*   | _  => app (getDigitList (Zdiv z 10)) [Zmod z 10] *)
(*   end. *)

Fixpoint charList_of_expr(e:expr): string :=
  match e with
  | V n => "(V " ++ (string_of_nat n) ++ ")"
  | L e => "(L " ++ (charList_of_expr e) ++ ")"
  | A e1 e2 =>
    "(A (" ++ (charList_of_expr e1) ++ ") " ++
       "(" ++ (charList_of_expr e2) ++"))"
  end.

Example charList_of_expr_ex1: charList_of_expr (V 0) = "(V 0)".
Proof. reflexivity. Qed.

Example charList_of_expr_ex2: charList_of_expr (L (V 0)) = "(L (V 0))".
Proof. reflexivity. Qed.

Fixpoint expr_eq(e1 e2:expr) : bool :=
  match e1, e2 with
  | (V n1), (V n2) => beq_nat n1 n2
  | (L t1), (L t2) => expr_eq t1 t2
  | (A t1 t2), (A s1 s2) => andb (expr_eq t1 s1) (expr_eq t2 s2)
  | _, _ => false
  end.

Example expr_eq_test1: expr_eq (L (V 0)) (L (V 0)) = true.
Proof. reflexivity. Qed.

Example expr_eq_test2: expr_eq (L (V 0)) (L (V 1)) = false.
Proof. reflexivity. Qed.

Definition i : expr := L (V 0).
Definition k : expr := L (L (V 1)).
Definition s : expr := L (L (L (A (A (V 2) (V 0)) (A (V 1) (V 0))))).

(* シフト *)
Definition termShift(d:Z)(t:expr) : expr :=
  ( fix walk(c:nat)(t:expr) :=
    match t with
    | V k => if ble_nat c k then V (Zabs_nat ((Z_of_nat k) + d)) else V k
    | L t1 => L (walk (S c) t1)
    | A t1 t2 => A (walk c t1) (walk c t2)
    end ) O t.

Goal termShift 2 (L (L (A (V 1) (A (V 0) (V 2))))) = (L (L (A (V 1) (A (V 0) (V 4))))).
Proof. reflexivity. Qed.

Goal termShift (-1) (termShift 1 (V 0)) = V 0.
Proof. reflexivity. Qed.

Goal termShift (-1) (termShift 1 (V 1)) = V 1.
Proof. reflexivity. Qed.

Goal termShift 2 (L (A (A (V 0) (V 1)) (L (A (A (V 0) (V 1)) (V 2))))) = (L (A (A (V 0) (V 3)) (L (A (A (V 0) (V 1)) (V 4))))).
Proof. reflexivity. Qed.

Goal forall(n:nat), termShift (-1) (termShift 1 (V n)) = V n.
Proof.
  induction n.
  unfold termShift.
  simpl.
  reflexivity.

  unfold termShift at 2.
  simpl.
  Abort.

(* 代入 *)
Definition termSubst(j:nat)(s t:expr) : expr := 
  ( fix walk(c:nat)(t:expr) :=
  match t with
  | V k => if (beq_nat k (j+c)) then termShift (Z_of_nat c) s else V k 
  | L t1 => L (walk (S c) t1)
  | A t1 t2 => A (walk c t1) (walk c t2)
  end ) O t.

Definition termSubstTop(s t:expr) := 
  termShift (-1) (termSubst 0 (termShift 1 s) t).

Fixpoint eval1(t:expr) : expr :=
  match t with
  | V _ => t
  | L _ => t
  | A t1 t2 => match t1, t2 with
               | (V _),    (V _) => t
               | (V _),    (L e) => (A t1 (L (eval1 e)))
               | (V _),  (A _ _) => (A t1 (eval1 t2))
               | (L e1),   (V _) => termSubstTop t2 e1
               | (L e1),   (L _) => termSubstTop t2 e1
               | (L e1), (A _ _) => termSubstTop t2 e1
               | (A _ _),  (V _) => A (eval1 t1) t2
               | (A _ _),  (L e) => A (eval1 t1) (L (eval1 e))
               | (A _ _), (A _ _)=> A (eval1 t1) (eval1 t2)
               end
  end.

Fixpoint eval(t:expr) : option expr :=
  ( fix eval'(t:expr)(step:nat) : option expr :=
  match step with
  | O => None
  | S step' => if expr_eq t (eval1 t) then Some t else eval' (eval1 t) step'
  end ) t 500.

Definition zero := (L (L (V 0))).
Definition one := (L (L (A (V 1) (V 0)))).
Definition two := (L (L (A (V 1) (A (V 1) (V 0))))).
Definition suc := (L (L (L (A (V 1) (A (A (V 2) (V 1)) (V 0)))))).
(* Definition pred :=  *)

Definition eCons(x y:expr) : expr := 
  L (A (A (V 0) x) y).
Definition eHead(lst:expr) := (A lst k).
Definition eTail(lst:expr) := (A lst (A k i)).

(* Eval compute in eval (A (A (eHead (eCons zero one)) (V 1)) (V 0)) . *)


Goal eval (eHead (eCons (V 1) (V 2))) = Some (V 0).
Proof.
  simpl.
  unfold termSubstTop.
  unfold termShift.
  simpl.
  reflexivity.
Qed.

Goal eval (eTail (eCons (V 1) (V 2))) = Some (V 0).
Proof.
  unfold eCons.
  unfold eTail.
  unfold k.
  unfold i.
  simpl.
  unfold termSubstTop.
  unfold termShift.
  simpl.
  unfold nat_of_P.
  simpl.
Abort.

Goal eval1 (A (L (A (A (V 1) (V 0)) (V 2))) (L (V 0))) = A (A (V 0) (L (V 0))) (V 1).
Proof. reflexivity. Qed.

Inductive isChurchNum : expr -> Prop :=
  | ch0 : isChurchNum (L (L (V 0)))
  | chA : forall(e:expr),
    isChurchNum (L (L e)) -> isChurchNum (L (L (A (V 1) e)))
.

Goal isChurchNum zero.
Proof.
  unfold zero.
  apply ch0.
Qed.

Goal isChurchNum one.
Proof.
  unfold one.  
  apply chA.
  apply ch0.
Qed.


Definition getOpt{X:Type}(s:option X)(d:X) : X :=
  match s with
  | Some s' => s'
  | None => d
  end.

Definition appChurchNum(e:expr): option expr :=
  (eval (A (A e (V 1)) (V 0))).

Fixpoint isChurchNumBool(e:expr) : bool :=
  let notChNum := (L (V 0)) in
  let e' := getOpt (appChurchNum e) notChNum in
  ( fix isChurchNumBool'(e:expr) : bool := 
    match e with
    | (V 0) => true
    | A (V 1) e' => isChurchNumBool' e'
    | _ => false
    end ) e'.


Goal isChurchNumBool zero = true.
Proof. reflexivity. Qed.
  
Goal isChurchNumBool one = true.
Proof. reflexivity. Qed.

Definition threeQ := (getOpt (eval (A suc two)) (L (V 1))).
Goal isChurchNumBool threeQ = true.
Proof. reflexivity. Qed.

(* (標準入力の)文字列をバイト列に変換する *)
Fixpoint byteList_of_string(s:string) : list nat :=
  let EOS := 256 in
  match s with
  | EmptyString => [EOS]
  | String a s' => (nat_of_ascii a) :: byteList_of_string s'
  end.

Goal byteList_of_string "ABC" = [65, 66, 67, 256].
Proof. reflexivity. Qed.

(* 自然数をチャーチ数に変換する *)
Fixpoint church_of_nat(n:nat) : expr :=
  match n with
  | O => zero
  | S n' => A suc (church_of_nat n')
  end.


Goal isChurchNumBool (getOpt (eval (church_of_nat 3)) (L (V 0))) = true.
Proof. reflexivity. Qed.
 
Definition churchList_of_string(s:string) : list expr :=
  map church_of_nat (byteList_of_string s).


Fixpoint expr_of_exprList(l:list expr) : expr :=
  let EOS := 256 in 
  match l with
  | nil => church_of_nat EOS
  | h :: t => eCons h (expr_of_exprList t)
  end.

(* OCamlで使う *)
Definition expr_of_string(s:string) : expr := expr_of_exprList (churchList_of_string s).

Fixpoint nat_of_churchNum(e:expr) : option nat :=
  if isChurchNumBool e
    then
      Some ((fix count(e:expr): nat := 
       match e with
       | (V 0) => 0
       | A (V 1) e' => S (count e')
       | _ => 0
       end
      ) (getOpt (appChurchNum e) i))
    else None.

Example nat_of_churchNum_0: nat_of_churchNum zero = Some 0.
Proof. reflexivity. Qed.

Example nat_of_churchNum_1: nat_of_churchNum one = Some 1.
Proof. reflexivity. Qed.

(* 2つの変数を適用して評価した結果で判定する *)
(* exprの構成そのもので判定するわけではない*)
Fixpoint church_num_eq(e1 e2:expr): bool :=
  let e1' := appChurchNum e1 in
  let e2' := appChurchNum e2 in
  match e1', e2' with
  | Some exp1, Some exp2 => expr_eq exp1 exp2
  | Some _, None => false
  | None, Some _ => false
  | None, None => false
  end.

Fixpoint string_of_churchStream(lst:expr): string :=
( fix string_of_churchStream'(lst:expr)(step:nat): string :=
  let EOS : nat := 256 in
  match step with
  | O => EmptyString
  | S step' => let hdAscii := (getOpt (nat_of_churchNum (eHead lst)) EOS) in
    if beq_nat hdAscii EOS then EmptyString else String (ascii_of_nat hdAscii) (string_of_churchStream' (eTail lst) step')
  end ) lst 500.

Example church_num_eq_test1: church_num_eq (A suc zero) one = true.
Proof. reflexivity. Qed.

Example church_num_eq_test2: church_num_eq (A suc zero) zero = false.
Proof. reflexivity. Qed.

Goal church_num_eq (eHead (eCons zero one)) zero = true.
Proof. reflexivity. Qed.

Goal church_num_eq (eHead (eCons zero one)) zero = true.
Proof. reflexivity. Qed.

Goal church_num_eq (eTail (eCons zero one)) one = true.
Proof. reflexivity. Qed.

Goal church_num_eq (eTail (eCons zero one)) zero = false.
Proof. reflexivity. Qed.

Goal forall(x y:expr),
  church_num_eq (eHead (eCons x y)) x = true.
Proof. 
  intros x y.
  unfold eCons.
  unfold eHead.
Abort.  
  
Goal forall(x y:expr),
  church_num_eq (eTail (eCons x y)) y = true.
Proof.
Abort.
(* reflexivity. Qed. *)

Inductive isSKI: expr -> Prop :=
  | eq_i : isSKI i
  | eq_k : isSKI k
  | eq_s : isSKI s
  | app_i : forall e:expr, isSKI e -> isSKI (A e i)
  | app_k : forall e:expr, isSKI e -> isSKI (A e k)
  | app_s : forall e:expr, isSKI e -> isSKI (A e s)
.

(* Ltac isSKI_tac: *)

Example isSKI_ex1: isSKI (A s i).
Proof.
  apply app_i.
  apply eq_s.
Qed.

(* End Sec. *)
End Lz.

Extract Inductive option => "option" ["Some" "None"].
Extraction "lazykoq.ml" Lz.
