From Stdlib Require Import List.
From CakeML Require Import ast namespace semanticPrimitives functions bigstep.

Ltac det_step :=
  match goal with
  | IH : forall r2, evaluate ?env ?e r2 -> _ = r2, H : evaluate ?env ?e _ |- _ =>
      apply IH in H; inversion H; subst; clear H
  | IH : forall r2, evaluate_list ?env ?es r2 -> _ = r2, H : evaluate_list ?env ?es _ |- _ =>
      apply IH in H; inversion H; subst; clear H
  | IH : forall r2, evaluate_match ?env ?v ?pes ?err r2 -> _ = r2, H : evaluate_match ?env ?v ?pes ?err _ |- _ =>
      apply IH in H; inversion H; subst; clear H
  | H1 : ?x = Some _, H2 : ?x = Some _ |- _ =>
      rewrite H1 in H2; inversion H2; subst; clear H2
  | H1 : ?x = Match _ _, H2 : ?x = Match _ _ |- _ =>
      rewrite H1 in H2; inversion H2; subst; clear H2
  | H1 : ?x = Match _ _, H2 : ?x = No_match _ |- _ =>
      rewrite H1 in H2; discriminate H2
  end.

Lemma evaluate_deterministic env :
  (forall e r1, evaluate env e r1 -> forall r2, evaluate env e r2 -> r1 = r2) /\
  (forall es r1, evaluate_list env es r1 -> forall r2, evaluate_list env es r2 -> r1 = r2) /\
  (forall v pes err r1, evaluate_match env v pes err r1 -> forall r2, evaluate_match env v pes err r2 -> r1 = r2).
Proof.
  apply (evaluate_mutual_ind
    (fun env e r1 _ => forall r2, evaluate env e r2 -> r1 = r2)
    (fun env es r1 _ => forall r2, evaluate_list env es r2 -> r1 = r2)
    (fun env v pes err r1 _ => forall r2, evaluate_match env v pes err r2 -> r1 = r2)); intros; match goal with H : _ |- _ => inversion H; subst end;
    repeat det_step; try congruence; try reflexivity.
Qed.

Lemma evaluate_det env e r1 r2 :
  evaluate env e r1 -> evaluate env e r2 -> r1 = r2.
Proof. intros H1 H2. now apply (proj1 (evaluate_deterministic env) _ _ H1). Qed.
