Require Import List.
Require Import EqNat.
Require Import Ascii String.
Require Import ZArith.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.
(* Require Import Tokenizer. *)


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

Module Lazykoq.

(* ラムダ式 *)
Inductive expr : Type :=
  | V : nat -> expr
  | L : expr -> expr
  | A : expr -> expr -> expr
.

Open Scope string_scope.
Fixpoint string_of_expr(e:expr): string :=
  match e with
  | V n => "(V " ++ (String (ascii_of_nat (n + 48)) ")")
  | L e => "(L " ++ (string_of_expr e) ++ ")"
  | A e1 e2 =>
    "(A (" ++ (string_of_expr e1) ++ ") " ++
       "(" ++ (string_of_expr e2) ++"))"
  end.

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
Fixpoint string_to_byte(s:string) : list nat :=
  let EOF := 256 in
  match s with
  | EmptyString => [EOF]
  | String a s' => (nat_of_ascii a) :: string_to_byte s'
  end.

(* 自然数をチャーチ数に変換する *)
Fixpoint church_of_nat(n:nat) : expr :=
  match n with
  | O => zero
  | S n' => A suc (church_of_nat n')
  end.


Goal isChurchNumBool (getOpt (eval (church_of_nat 3)) (L (V 0))) = true.
Proof. reflexivity. Qed.
 
Definition string_to_church_list(s:string) : list expr :=
  map church_of_nat (string_to_byte s).

Fixpoint listExpr_to_Expr(l:list expr) : expr :=
  let EOF := 256 in 
  match l with
  | nil => church_of_nat EOF
  | h :: t => eCons h (listExpr_to_Expr t)
  end.

Fixpoint church_num_to_nat(e:expr) : option nat :=
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

Example church_num_to_nat_0: church_num_to_nat zero = Some 0.
Proof. reflexivity. Qed.

Example church_num_to_nat_1: church_num_to_nat one = Some 1.
Proof. reflexivity. Qed.

Fixpoint church_stream_to_string(lst:expr)(step:nat): string :=
  let EOF : nat := 256 in
  match step with
  | O => EmptyString
  | S step' => let anat := (getOpt (church_num_to_nat (eHead lst)) EOF) in if beq_nat anat EOF then EmptyString else String (ascii_of_nat anat) (church_stream_to_string (eTail lst) step')
  end.

End Lazykoq.
(* Example tokenize_ex2 : *)
(*     Tokenizer.tokenize "(S K) K" %string *)
(*   = ["(", "S", "K", ")", "K"]%string. *)
(* Proof. reflexivity. Qed. *)

(* Definition isCombinator(c : ascii) : bool := *)
(*   let n := nat_of_ascii c in *)
(*   (orb (beq_nat n 83) (orb (beq_nat n 75) (orb (beq_nat n 73) *)
(*        (orb (beq_nat n 115) (orb (beq_nat n 107) (beq_nat n 105)))))). *)

(* Example sisCombinatorCap: isCombinator "S"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example SisCombinatorSm: isCombinator "s"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example KisCombinatorCap: isCombinator "K"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example KisCombinatorSm: isCombinator "k"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example IisCombinatorCap: isCombinator "I"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example IisCombinatorSm: isCombinator "i"%char = true. *)
(* Proof. reflexivity. Qed. *)

(* Example AisNotCombinator: isCombinator "a"%char = false. *)
(* Proof. reflexivity. Qed. *)


Extraction "lazykoq.ml" Lazykoq.
