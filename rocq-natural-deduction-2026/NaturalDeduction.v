(* Natural Deduction *)
Lemma Le : forall A B C: Prop, (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  intros A B C. unfold "<->". split. (* split позволяет разделить цель на подцели *)
  - (* при помощи буллетов - + * и т.п. можно фокусироваться на подцелях *)
    intro Habc. split.
    + intro a. apply Habc. (* тактика apply позволяет применить известную теорему или гипотезу из контекста: если в цели следствие теоремы, она трансформирует цель так, что нужно доказать посылку теоремы *)
      left. (* left и right позволяют выбирать конкретный член дизъюнкции, который мы можем доказать *)
      exact a.
      (* Undo.
      apply a. *)
    + intro b. apply Habc. right. exact b.
  - intros H1 H2.
    elim H1. intros Hac Hbc. elim H2.
    + intros a. apply Hac. exact a.
    + intros b. apply Hbc. exact b.
Qed.

Lemma Le2 : forall A B C: Prop, (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  intros A B C. unfold "<->". split. 
    - intro Habc. split.
    + intro a. apply Habc. 
      left. 
      exact a.
    + intro b. apply Habc. right. exact b.

    (* из H1 хочется получить две отдельных гипотезы, а в H2 понять, что именно выполняется. это можно сделать при помощи intro-паттернов: https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns *)
  - intros [Hac Hbc] [Ha | Hb].
    + specialize (Hac Ha). exact Hac.
    + apply Hbc. assumption. (* если цель находится среди гипотез, можно не указывать её конкретно при помощи exact, а просто вызвать тактику assumption *)
Qed.

Print True. (* True - тип с одним конструктором без аргументов: I *)
Print False. (* False - тип без конструкторов *)

Theorem True_can_be_proven : True.
  exact I.
Qed.

Theorem Ex_Falso : forall A, False -> A.
Proof. intros A H. elim H. Qed.

(* Отрицание в Coq реализовано как импликация в ложь. Подробнее об этом, когда на лекциях будем говорить про интуиционисткую логику. *)
Print "~".

(* Ложь - то, что никогда не может быть доказано. *)
Theorem False_cannot_be_proven__again : ~False.
Proof.
  unfold "~". (* тактика unfold позволяет раскрывать определения и синтаксический сахар *)
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven__again_2 : ~False.
Proof.
  unfold "~". 
  intros proof_of_False.
  (* если ложь оказалась в контексте, из неё следует что угодно: с точки зрения типов у нас есть терм типа, у которого нет конструкторов! это невозможно, поэтому можно доказать что угодно. *)
  elim proof_of_False. (* тактика elim позволяет разобрать возможные случаи, какими конструкторами был построен терм. поскольку у типа False нет конструкторов, elim рассматривает 0 случаев, а поэтому доказательство завершается! *)
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  intros P H G. (* синтаксический сахар для отрицания автоматически раскрывается в импликацию, когда используем intros *)
  apply G. apply H.
Qed.

(* Exercise *)
Theorem backward_huge : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
  intros A B C.
  intros H1 H2 H3.
  apply H3.
  - assumption.
  - apply H2. assumption.
Qed.

(* Exercise *)
Lemma distributivity_of_disjunction_over_conjunction:
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  unfold "<->". split.
  - intros [H1 | H2].
    + split.
      * left. assumption.
      * left. assumption.
    + split.
      * right. apply H2.
      * right. apply H2.
  - intros [[HA | HB] [HA' | HC]].
    + left. assumption.
    + left. assumption.
    + left. assumption.
    + right. split.
      * assumption.
      * assumption.
Qed.

(* Exercise *)
Lemma Curry_and_unCurry : forall P Q R : Prop, (P /\ Q -> R) <-> (P -> Q -> R).
Proof.
  intros P Q R. unfold "<->". split.
  - intros H1 H2 H3. apply H1. split.
    + assumption.
    + assumption.
  - intros H1 H2.
    + apply H1.
      * apply H2.
      * apply H2.
Qed.

(* Exercise *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q. unfold "~".
  intros H1 H2 H3.
  apply H2. apply H1. assumption. 
Qed.

(* Exercise *)
Theorem de_morgan_not_or : forall (P Q : Prop), ~ (P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q. unfold "<->". unfold "~". split.
  - intros H1. split.
    + intros Hp. elim H1. left. assumption.
    + intros Hq. elim H1. right. assumption.
  - intros [H1 H2] [H3 | H4].
    + apply H1. assumption.
    + apply H2. assumption. 
Qed.
