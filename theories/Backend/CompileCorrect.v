From MetaRocq.Utils Require Import utils.
From Stdlib Require Import List String.
Import ListNotations.
Local Open Scope string_scope.
From MetaRocq.Utils Require Import ReflectEq bytestring MRList.
From MetaRocq Require Import EWcbvEvalNamed.

From CakeML Require Import Compile bigstep.

From CakeML Require Import ast namespace.
From CakeML Require Import semanticPrimitives.

From Equations Require Import Equations.

Definition lookup {A} (E : list (Kernames.ident * A)) (x : string) :=
  match find (fun '(s, _) => String.eqb x s) E with
  | Some (_, v) => Some v
  | None => None
  end.

Definition fail str := Litv (StrLit str).

(* compile_value now takes a constructor environment parameter cenv,
   so that closures capture the right constructor namespace.
   Also, TypeStamp uses 0 as the type identifier (not the constructor index). *)
Fixpoint compile_value (Σ : EAst.global_declarations) (cenv : env_ctor) (s : EWcbvEvalNamed.value) : val.
  refine (
  match s with
  | vClos na b env => Closure _ (String.to_string na) (compile Σ b)
  | vConstruct i m args =>
      match lookup_constructor_names Σ i with
      | Some names => match nth_error names m with
                     | Some name => Conv (Some (TypeStamp (String.to_string name) 0)) (map (compile_value Σ cenv) args)
                     | None => fail "constructor not found"
                     end
      | None => fail "type not found"
      end
  | vRecClos mfix idx env =>
       Recclosure _
              (map (fun '(recn, b) =>
                let '(arg, expr) := force_lambda (compile Σ b) in
                (String.to_string recn, arg, expr)
              ) mfix)
              (match nth_error mfix idx with Some (id, _) => String.to_string id | _ => "fail" end)
  | vPrim v => fail "no primitives supported"
  | vLazy t l => fail "lazy not supported"
  end).
- econstructor.
  econstructor.
  eapply map. 2: exact env.
  intros []. econstructor.
  apply (String.to_string i).
  apply compile_value; assumption.
  exact [].
  exact cenv.
- econstructor.
  econstructor.
  eapply map. 2: exact env.
  intros []. econstructor.
  apply (String.to_string i).
  apply compile_value; assumption.
  exact [].
  exact cenv.
Defined.

From Stdlib Require Import FunctionalExtensionality.

Lemma to_string_of_string s :
  String.to_string (String.of_string s) = s.
Proof.
  induction s; cbn.
  - reflexivity.
  - now rewrite Ascii.ascii_of_byte_of_ascii, IHs.
Qed.

Lemma of_string_to_string s :
  String.of_string (String.to_string s) = s.
Proof.
  induction s; cbn.
  - reflexivity.
  - now rewrite Ascii.byte_of_ascii_of_byte, IHs.
Qed.

Lemma lookup_map {A B} (f : A -> B) Γ x :
  lookup (map (fun '(x0, v) => (x0, f v)) Γ) x = option_map f (lookup Γ x).
Proof.
  unfold lookup.
  induction Γ as [ | []].
  - reflexivity.
  - cbn in *. change (String.eqb x i) with (eqb x i). destruct (eqb_spec x i).
    + subst. reflexivity.
    + eapply IHΓ.
Qed.

Lemma lookup_add a v Γ na :
  lookup (add a v Γ) na = if na == a then Some v else lookup Γ na.
Proof.
  unfold add, lookup. cbn. change (String.eqb na a) with (na == a).
  destruct (eqb_spec na a); congruence.
Qed.

From Stdlib Require Import Lia.

Lemma lookup_multiple nms args Γ na :
  List.length nms = List.length args ->
  lookup (add_multiple nms args Γ) na = match find (fun x => na == fst x) (map2 pair nms args) with
                                        | Some (_, y) => Some y
                                        | None => lookup Γ na
                                        end.
Proof.
  intros Hlen. induction nms in args, Hlen |- *.
  - destruct args; cbn in *; congruence.
  - destruct args; cbn in *; try congruence.
    rewrite lookup_add, IHnms. 2: cbn in *; lia.
    destruct (eqb_spec na a).
    + eauto.
    + reflexivity.
Qed.

Lemma lookup_env_In d Σ :
  EGlobalEnv.lookup_env Σ (fst d) = Some (snd d) -> In d Σ.
Proof.
  induction Σ; cbn in *.
  - congruence.
  - destruct (eqb_spec (fst d) (fst a)). intros [=]. destruct a, d; cbn in *; intuition auto.
    left; subst; auto.
    intros hl; specialize (IHΣ hl); intuition auto.
Qed.

Lemma All2_nth_error_Some_right {A B} {P : A -> B -> Type} {l l'} n t :
  All_Forall.All2 P l l' ->
  nth_error l' n = Some t ->
  { t' : A & (nth_error l n = Some t') * P t' t}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists x. intuition auto.
  eauto.
Qed.

Lemma nth_error_fix_env idx mfix Γ :
  idx < #|mfix| ->
  nth_error (fix_env mfix Γ) idx = Some (vRecClos mfix (#|mfix| - S idx) Γ).
Proof.
  unfold fix_env. induction #|mfix| in idx |- *; cbn.
  - lia.
  - intros. destruct idx.
    + cbn. now rewrite Nat.sub_0_r.
    + cbn. eapply IHn. lia.
Qed.

Definition extraction_env_flags_mlf :=
  let nolazy_array_term_flags := {|
    EWellformed.has_tBox := false;
    EWellformed.has_tRel := true;
    EWellformed.has_tVar := false;
    EWellformed.has_tEvar := false;
    EWellformed.has_tLambda := true;
    EWellformed.has_tLetIn := true;
    EWellformed.has_tApp := true;
    EWellformed.has_tConst := true;
    EWellformed.has_tConstruct := true;
    EWellformed.has_tCase := true;
    EWellformed.has_tProj := false;
    EWellformed.has_tFix := true;
    EWellformed.has_tCoFix := false;
    EWellformed.has_tPrim :=
      {| EWellformed.has_primint := true;
         EWellformed.has_primfloat := true;
         EWellformed.has_primstring := false;
         EWellformed.has_primarray := false |};
    EWellformed.has_tLazy_Force := false
  |}
  in
  {|
  EWellformed.has_axioms := false;
  EWellformed.has_cstr_params := false;
  EWellformed.term_switches := nolazy_array_term_flags;
  EWellformed.cstr_as_blocks := true |}.

Fixpoint id_to_string (i : id) :=
  match i with
  | Short n => String.of_string n
  | Long m nm => String.of_string m ++ "." ++ id_to_string nm
  end.

(* The CakeML environment constructed from a source environment *)
Definition compile_env (Σ : EAst.global_declarations) (cenv : env_ctor) (Γ : EWcbvEvalNamed.environment) : Sem_env val :=
  {| v := Bind modN varN val (map (fun '(id, v0) => (String.to_string id, compile_value Σ cenv v0)) Γ) [];
     c := cenv |}.

(* The constructor environment is set up correctly for all constructors in Σ *)
Definition ctor_env_ok (Σ : EAst.global_declarations) (cenv : env_ctor) : Prop :=
  forall ind mdecl idecl c cdecl,
    EGlobalEnv.lookup_inductive Σ ind = Some (mdecl, idecl) ->
    nth_error (EAst.ind_ctors idecl) c = Some cdecl ->
    nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl))) =
      Some (EAst.cstr_nargs cdecl, TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0).

(* Constructor names are distinct within each inductive type *)
Definition cstr_names_distinct (Σ : EAst.global_declarations) : Prop :=
  forall ind mdecl idecl,
    EGlobalEnv.lookup_inductive Σ ind = Some (mdecl, idecl) ->
    List.NoDup (map EAst.cstr_name (EAst.ind_ctors idecl)).

(* The compile_env satisfies the environment correspondence *)
Lemma compile_env_lookup Σ cenv Γ n :
  nsLookup _ (v val (compile_env Σ cenv Γ)) (Short (String.to_string n)) =
  match EWcbvEvalNamed.lookup Γ n with
  | Some v => Some (compile_value Σ cenv v)
  | None => None
  end.
Proof.
  unfold compile_env, EWcbvEvalNamed.lookup. cbn.
  induction Γ as [| [id v0] Γ' IH]; cbn.
  - reflexivity.
  - destruct (String.eqb_spec (String.to_string id) (String.to_string n)) as [Heq|Hneq].
    + apply (f_equal String.of_string) in Heq.
      rewrite !of_string_to_string in Heq. subst.
      change (String.eqb n n) with (n == n).
      now rewrite eqb_refl.
    + assert (Hne : n <> id).
      { intro Heq; subst; congruence. }
      change (String.eqb n id) with (n == id).
      destruct (eqb_spec n id); [congruence | exact IH].
Qed.

(* Extending compile_env with a binding *)
Lemma compile_env_add Σ cenv na v' Γ :
  {| v := nsBind (String.to_string na) (compile_value Σ cenv v') (v val (compile_env Σ cenv Γ));
     c := c val (compile_env Σ cenv Γ) |} = compile_env Σ cenv (add na v' Γ).
Proof.
  unfold compile_env, add, nsBind. cbn. reflexivity.
Qed.


(* consts_ok says all global constants' evaluated values are in the source env *)
Definition consts_ok (Σ : EAst.global_declarations) (Γ : EWcbvEvalNamed.environment) : Prop :=
  forall c decl body res,
    EGlobalEnv.declared_constant Σ c decl ->
    EAst.cst_body decl = Some body ->
    EWcbvEvalNamed.eval Σ [] body res ->
    EWcbvEvalNamed.lookup Γ (Kernames.string_of_kername c) = Some res.

Lemma consts_ok_add Σ Γ na v0 :
  consts_ok Σ Γ ->
  (forall c decl, EGlobalEnv.declared_constant Σ c decl ->
    Kernames.string_of_kername c <> na) ->
  consts_ok Σ (add na v0 Γ).
Proof.
  unfold consts_ok, add. intros H Hnoshadow c decl body res Hdecl Hbody Hev.
  specialize (H c decl body res Hdecl Hbody Hev).
  unfold EWcbvEvalNamed.lookup in *. cbn.
  change (String.eqb (Kernames.string_of_kername c) na) with
    (Kernames.string_of_kername c == na).
  destruct (eqb_spec (Kernames.string_of_kername c) na); auto.
  exfalso. eapply Hnoshadow; eauto.
Qed.

Lemma consts_ok_add_multiple Σ Γ nms vs :
  consts_ok Σ Γ ->
  (forall na, In na nms -> forall c decl, EGlobalEnv.declared_constant Σ c decl ->
    Kernames.string_of_kername c <> na) ->
  consts_ok Σ (add_multiple nms vs Γ).
Proof.
  revert vs. induction nms; intros vs Hok Hnoshadow; destruct vs; cbn; auto.
  apply consts_ok_add.
  - apply IHnms; auto. intros na Hin c0 decl0 Hdecl0. eapply Hnoshadow. right; exact Hin. exact Hdecl0.
  - intros c0 decl0 Hdecl0. eapply Hnoshadow. left; reflexivity. exact Hdecl0.
Qed.

(* Fresh name: not equal to any constant's kernel name *)
Definition fresh_name (Σ : EAst.global_declarations) (na : Kernames.ident) : Prop :=
  forall c decl, EGlobalEnv.declared_constant Σ c decl ->
  Kernames.string_of_kername c <> na.

(* Well-formed term: no prim/lazy/force, and all binder names are fresh for constants *)
Inductive wf_term (Σ : EAst.global_declarations) : EAst.term -> Prop :=
| wf_tBox : wf_term Σ EAst.tBox
| wf_tRel n : wf_term Σ (EAst.tRel n)
| wf_tVar na : wf_term Σ (EAst.tVar na)
| wf_tEvar n l : (forall t, In t l -> wf_term Σ t) -> wf_term Σ (EAst.tEvar n l)
| wf_tLambda nm b :
    fresh_name Σ (BasicAst.string_of_name nm) ->
    wf_term Σ b ->
    wf_term Σ (EAst.tLambda nm b)
| wf_tLetIn nm d b :
    fresh_name Σ (BasicAst.string_of_name nm) ->
    wf_term Σ d -> wf_term Σ b ->
    wf_term Σ (EAst.tLetIn nm d b)
| wf_tApp f a : wf_term Σ f -> wf_term Σ a -> wf_term Σ (EAst.tApp f a)
| wf_tConst c : wf_term Σ (EAst.tConst c)
| wf_tConstruct ind c args :
    (forall mdecl idecl cdecl,
      EGlobalEnv.lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      #|args| = EAst.cstr_nargs cdecl) ->
    (forall t, In t args -> wf_term Σ t) ->
    #|args| <= 1 ->
    wf_term Σ (EAst.tConstruct ind c args)
| wf_tCase ind mch brs :
    wf_term Σ mch ->
    (forall binders b, In (binders, b) brs ->
      (forall x, In x binders -> fresh_name Σ (BasicAst.string_of_name x)) /\
      wf_term Σ b /\
      List.NoDup (map (fun x => BasicAst.string_of_name x) binders)) ->
    (forall mdecl idecl,
      EGlobalEnv.lookup_inductive Σ (fst ind) = Some (mdecl, idecl) ->
      #|brs| = #|EAst.ind_ctors idecl| /\
      forall i binders body cdecl0,
        nth_error brs i = Some (binders, body) ->
        nth_error (EAst.ind_ctors idecl) i = Some cdecl0 ->
        #|binders| = EAst.cstr_nargs cdecl0) ->
    wf_term Σ (EAst.tCase ind mch brs)
| wf_tProj p t : wf_term Σ t -> wf_term Σ (EAst.tProj p t)
| wf_tFix mfix idx :
    (forall d, In d mfix ->
      fresh_name Σ (BasicAst.string_of_name (EAst.dname d)) /\
      wf_term Σ (EAst.dbody d)) ->
    #|mfix| <= 1 ->
    wf_term Σ (EAst.tFix mfix idx)
| wf_tCoFix mfix idx :
    wf_term Σ (EAst.tCoFix mfix idx).

(* Well-formed value: closures capture well-formed environments *)
Inductive val_ok (Σ : EAst.global_declarations) : EWcbvEvalNamed.value -> Prop :=
| val_ok_Clos na b Γ :
    fresh_name Σ na ->
    wf_term Σ b ->
    consts_ok Σ Γ ->
    (forall na' v, EWcbvEvalNamed.lookup Γ na' = Some v -> val_ok Σ v) ->
    val_ok Σ (vClos na b Γ)
| val_ok_RecClos mfix idx Γ :
    (forall n b, In (n, b) mfix -> fresh_name Σ n /\ wf_term Σ b) ->
    consts_ok Σ Γ ->
    (forall na' v, EWcbvEvalNamed.lookup Γ na' = Some v -> val_ok Σ v) ->
    #|mfix| <= 1 ->
    val_ok Σ (vRecClos mfix idx Γ)
| val_ok_Construct i m args :
    (forall v, In v args -> val_ok Σ v) ->
    #|args| <= 1 ->
    val_ok Σ (vConstruct i m args)
| val_ok_Prim v : val_ok Σ (vPrim v)
| val_ok_Lazy t l : val_ok Σ (vLazy t l).

(* Well-formed environment: consts_ok + all values are val_ok *)
Definition env_ok (Σ : EAst.global_declarations) (Γ : EWcbvEvalNamed.environment) : Prop :=
  consts_ok Σ Γ /\ forall na v, EWcbvEvalNamed.lookup Γ na = Some v -> val_ok Σ v.

(* All constant bodies are well-formed terms *)
Definition wf_globals (Σ : EAst.global_declarations) : Prop :=
  forall c decl body,
    EGlobalEnv.declared_constant Σ c decl ->
    EAst.cst_body decl = Some body ->
    wf_term Σ body.

(* All constant values are well-formed *)
Definition consts_val_ok (Σ : EAst.global_declarations) : Prop :=
  forall c decl body res,
    EGlobalEnv.declared_constant Σ c decl ->
    EAst.cst_body decl = Some body ->
    EWcbvEvalNamed.eval Σ [] body res ->
    val_ok Σ res.

(* env_ok is preserved by adding a binding with a fresh name *)
Lemma env_ok_add Σ Γ na v0 :
  env_ok Σ Γ -> val_ok Σ v0 -> fresh_name Σ na -> env_ok Σ (add na v0 Γ).
Proof.
  intros [Hconst Hvals] Hval Hfresh. split.
  - apply consts_ok_add; auto.
  - intros na' v'. unfold EWcbvEvalNamed.lookup, add. cbn.
    change (String.eqb na' na) with (na' == na).
    destruct (eqb_spec na' na).
    + intros [= <-]. exact Hval.
    + exact (Hvals na' v').
Qed.

Lemma lookup_constructor_decompose Σ0 ind c mdecl idecl cdecl :
  EGlobalEnv.lookup_constructor Σ0 ind c = Some (mdecl, idecl, cdecl) ->
  EGlobalEnv.lookup_inductive Σ0 ind = Some (mdecl, idecl) /\
  nth_error (EAst.ind_ctors idecl) c = Some cdecl.
Proof.
  unfold EGlobalEnv.lookup_constructor, bind, Monad_option.
  destruct (EGlobalEnv.lookup_inductive Σ0 ind) as [[m i]|]; [|discriminate].
  intro H.
  assert (Hmi : (m, i) = (mdecl, idecl)).
  { destruct (nth_error (EAst.ind_ctors i) c) as [cd|]; [|discriminate].
    injection H. intros. subst. reflexivity. }
  inversion Hmi; subst m i. clear Hmi.
  destruct (nth_error (EAst.ind_ctors idecl) c) as [cd|]; [|discriminate].
  split; [reflexivity | injection H; intros; subst; reflexivity].
Qed.

Lemma compile_value_construct Σ0 cenv ind c args names name :
  lookup_constructor_names Σ0 ind = Some names ->
  nth_error names c = Some name ->
  compile_value Σ0 cenv (vConstruct ind c args) =
    Conv (Some (TypeStamp (String.to_string name) 0)) (map (compile_value Σ0 cenv) args).
Proof.
  intros Hnames Hnth. simpl. rewrite Hnames, Hnth. reflexivity.
Qed.

Lemma nth_error_nth_default {A} n (l : list A) d x :
  nth_error l n = Some x -> nth n l d = x.
Proof.
  revert n. induction l; destruct n; simpl; try discriminate.
  - intros [= ->]. reflexivity.
  - apply IHl.
Qed.

Lemma nth_error_map_In {A B} (f : A -> B) n (l : list A) x :
  nth_error l n = Some x ->
  nth_error (map f l) n = Some (f x).
Proof.
  revert n. induction l; destruct n; simpl; try discriminate.
  - intros [= ->]. reflexivity.
  - apply IHl.
Qed.

Lemma nth_error_map_inv {A B} (f : A -> B) n l y :
  nth_error (map f l) n = Some y ->
  exists x, nth_error l n = Some x /\ y = f x.
Proof.
  revert n. induction l; destruct n; simpl; try discriminate.
  - intros [= <-]. eauto.
  - apply IHl.
Qed.

Lemma In_map2_idx {A B C} (f : A -> B -> C) l1 l2 z :
  In z (map2 f l1 l2) ->
  exists i x y, nth_error l1 i = Some x /\ nth_error l2 i = Some y /\ z = f x y.
Proof.
  revert l2. induction l1; intros [|b l2]; simpl; try (intros []; fail).
  intros [Heq | Hin].
  - subst. exists 0, a, b. auto.
  - destruct (IHl1 l2 Hin) as [i [x [y [H1 [H2 H3]]]]].
    exists (S i), x, y. auto.
Qed.

Lemma evaluate_list_app env es1 es2 vs1 vs2 :
  evaluate_list env es1 (Rval_l vs1) ->
  evaluate_list env es2 (Rval_l vs2) ->
  evaluate_list env (List.app es1 es2) (Rval_l (List.app vs1 vs2)).
Proof.
  induction es1 in vs1 |- *; intros H1 H2.
  - inversion H1; subst. exact H2.
  - inversion H1; subst; try discriminate.
    simpl. econstructor; eauto.
Qed.

Lemma evaluate_list_singleton env e v :
  evaluate env e (Rval v) ->
  evaluate_list env [e] (Rval_l [v]).
Proof.
  intros. econstructor; [exact H | econstructor].
Qed.

Lemma rev_is_List_rev {A} (l : list A) : rev l = List.rev l.
Proof.
  induction l; [reflexivity | rewrite rev_cons, IHl; reflexivity].
Qed.

Lemma rev_rev {A} (l : list A) : rev (rev l) = l.
Proof. rewrite !rev_is_List_rev. apply List.rev_involutive. Qed.

From CakeML Require Import functions.

(* NOT_MEM_rel <-> ~ In *)
Lemma NOT_MEM_rel_not_In {A} (e : A) (l : list A) :
  NOT_MEM_rel A e l <-> ~ In e l.
Proof.
  induction l; split; intros.
  - intros [].
  - constructor.
  - inversion H; subst. intros [Heq | Hin].
    + subst; contradiction.
    + apply IHl in H4. contradiction.
  - constructor.
    + intros Heq; subst; apply H; left; reflexivity.
    + apply IHl; intros Hin; apply H; right; exact Hin.
Qed.

(* NoDup -> ALL_DISTINCT_rel *)
Lemma NoDup_ALL_DISTINCT_rel {A} (l : list A) :
  List.NoDup l -> ALL_DISTINCT_rel A l.
Proof.
  induction l; intros.
  - constructor.
  - inversion H; subst. constructor.
    + apply NOT_MEM_rel_not_In. assumption.
    + apply IHl. assumption.
Qed.

(* String.to_string is injective *)
Lemma to_string_injective (x y : bytestring.string) :
  String.to_string x = String.to_string y -> x = y.
Proof.
  intros H. apply (f_equal String.of_string) in H.
  rewrite !of_string_to_string in H. exact H.
Qed.

(* NoDup preserved by injective map *)
Lemma NoDup_map_injective {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) ->
  List.NoDup l -> List.NoDup (map f l).
Proof.
  intros Hinj. induction l; intros.
  - constructor.
  - inversion H; subst. constructor.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [x0 [Heq Hx0]].
      apply Hinj in Heq. subst. contradiction.
    + apply IHl. assumption.
Qed.

(* nsLookup after nsBind *)
Lemma nsLookup_nsBind_Short (name k : varN) (v0 : val) (ns : namespace modN varN val) :
  nsLookup val (nsBind k v0 ns) (Short name) =
    if (k =? name)%string then Some v0 else nsLookup val ns (Short name).
Proof.
  destruct ns. simpl. reflexivity.
Qed.

(* General fold_right nsBind In lookup *)
Lemma fold_nsBind_In (full : list (varN * varN * exp)) cl_env
  (base_var : list (varN * val)) (base_mods : list (modN * namespace modN varN val))
  (iter : list (varN * varN * exp)) (name : varN) :
  In name (map (fun '(x,_,_) => x) iter) ->
  nsLookup val (fold_right (fun '(f, _, _) (env' : namespace modN varN val) =>
    nsBind f (Recclosure cl_env full f) env') (Bind modN varN val base_var base_mods) iter) (Short name) =
    Some (Recclosure cl_env full name).
Proof.
  induction iter as [|[[f x0] e0] iter' IH].
  - simpl. intros [].
  - simpl. intros [Heq | Hin].
    + subst f.
      set (inner := fold_right _ _ _).
      destruct inner as [var mods].
      simpl. rewrite Strings.String.eqb_refl. reflexivity.
    + set (inner := fold_right _ _ _).
      destruct inner as [var mods] eqn:Hinner.
      simpl.
      destruct (Strings.String.eqb f name) eqn:Hfe.
      * apply Strings.String.eqb_eq in Hfe. subst. reflexivity.
      * specialize (IH Hin). unfold inner in Hinner.
        rewrite Hinner in IH. exact IH.
Qed.

(* build_rec_env lookup for In name *)
Lemma build_rec_env_In (funs : list (varN * varN * exp)) env (name : varN) :
  In name (map (fun '(x,_,_) => x) funs) ->
  nsLookup val (build_rec_env funs env (v val env)) (Short name) =
    Some (Recclosure env funs name).
Proof.
  unfold build_rec_env. destruct (v val env) as [bv bm].
  apply fold_nsBind_In.
Qed.

(* compile_fix_bodies: map_InP for tFix = map for vRecClos *)
Lemma compile_fix_bodies Σ0 (mfix : list (EAst.def EAst.term)) nms :
  Forall2 (fun d n => BasicAst.nNamed n = EAst.dname d) mfix nms ->
  List.map (fun d => let '(arg, expr) := force_lambda (compile Σ0 (EAst.dbody d)) in
    (String.to_string (BasicAst.string_of_name (EAst.dname d)), arg, expr)) mfix =
  List.map (fun '(recn, b) =>
    let '(arg, expr) := force_lambda (compile Σ0 b) in
    (String.to_string recn, arg, expr))
    (map2 (fun n d => (n, EAst.dbody d)) nms mfix).
Proof.
  induction 1; simpl.
  - reflexivity.
  - rewrite <- H. simpl.
    destruct (force_lambda (compile Σ0 (EAst.dbody x))).
    f_equal. exact IHForall2.
Qed.

(* Singleton fixpoint Var evaluation *)
Lemma evaluate_Var_singleton_rec (nm an : varN) (be : exp) (env : Sem_env val) :
  evaluate {| v := build_rec_env [(nm, an, be)] env (v val env); c := c val env |}
    (Var (Short nm)) (Rval (Recclosure env [(nm, an, be)] nm)).
Proof.
  eapply evaluate_Var.
  unfold build_rec_env. simpl.
  destruct (v val env) as [vl ml]. simpl.
  rewrite Strings.String.eqb_refl. reflexivity.
Qed.

Lemma compile_value_RecClos_singleton Σ0 cenv nm body Γ0 an be :
  force_lambda (compile Σ0 body) = (an, be) ->
  compile_value Σ0 cenv (vRecClos [(nm, body)] 0 Γ0) =
    Recclosure (compile_env Σ0 cenv Γ0) [(String.to_string nm, an, be)] (String.to_string nm).
Proof.
  intros Hfl. simpl. rewrite Hfl. simpl. reflexivity.
Qed.

Lemma force_lambda_compile_Lambda Σ0 na fn :
  force_lambda (compile Σ0 (EAst.tLambda (BasicAst.nNamed na) fn)) =
    (String.to_string na, compile Σ0 fn).
Proof. simp compile. reflexivity. Qed.

Lemma do_opapp_fix_unfold Σ0 cenv Γ' na na' fn av :
  do_opapp [compile_value Σ0 cenv (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ');
            compile_value Σ0 cenv av] =
    Some (compile_env Σ0 cenv
            (add na av (add na' (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ') Γ')),
          compile Σ0 fn).
Proof.
  unfold do_opapp, compile_env, add, build_rec_env.
  simpl compile_value. simp compile. simpl.
  rewrite Strings.String.eqb_refl.
  rewrite (force_lambda_compile_Lambda Σ0 na fn). simpl.
  reflexivity.
Qed.

From MetaRocq.Erasure Require Import EPrimitive.

Lemma compile_All2_evaluate_list Σ0 cenv Γ0 (args : list EAst.term) (args' : list EWcbvEvalNamed.value)
  (Ha : All2_Set (EWcbvEvalNamed.eval Σ0 Γ0) args args') :
  ctor_env_ok Σ0 cenv ->
  env_ok Σ0 Γ0 ->
  (forall t, In t args -> wf_term Σ0 t) ->
  wf_globals Σ0 ->
  consts_val_ok Σ0 ->
  All2_over Ha (fun (t : EAst.term) (v : EWcbvEvalNamed.value) (_ : EWcbvEvalNamed.eval Σ0 Γ0 t v) =>
    forall cenv', ctor_env_ok Σ0 cenv' -> env_ok Σ0 Γ0 -> wf_term Σ0 t ->
    evaluate (compile_env Σ0 cenv' Γ0) (compile Σ0 t) (Rval (compile_value Σ0 cenv' v)) /\ val_ok Σ0 v) ->
  evaluate_list (compile_env Σ0 cenv Γ0)
    (rev (map (compile Σ0) args))
    (Rval_l (rev (map (compile_value Σ0 cenv) args')))
  /\ (forall v, In v args' -> val_ok Σ0 v).
Proof.
  intros Hctor Henv Hwf_args Hwfg Hcvok IHa.
  induction Ha; simp All2_over in IHa.
  - simpl. split; [exact (evaluate_nil _) | intros v Hv; destruct Hv].
  - destruct IHa as [IHhd IHtl].
    assert (Hwf_x : wf_term Σ0 x) by (apply Hwf_args; left; reflexivity).
    specialize (IHhd cenv Hctor Henv Hwf_x) as [Hhd_eval Hhd_ok].
    assert (Hwf_rest : forall t, In t l -> wf_term Σ0 t) by (intros; apply Hwf_args; right; assumption).
    specialize (IHHa Hwf_rest IHtl) as [IHeval IHvok].
    split.
    + simpl map. rewrite !@rev_cons.
      apply evaluate_list_app; [exact IHeval |].
      exact (evaluate_list_singleton _ _ _ Hhd_eval).
    + intros v0 [Heq | Hin]; [subst; exact Hhd_ok | exact (IHvok v0 Hin)].
Qed.

(* Forall2 length *)
Lemma Forall2_length' {A B} {R : A -> B -> Prop} {l l'} :
  Forall2 R l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto; lia. Qed.

(* map2 facts *)
Lemma map2_length {A B C} (f : A -> B -> C) l1 l2 :
  #|l1| = #|l2| -> #|map2 f l1 l2| = #|l1|.
Proof.
  revert l2. induction l1; destruct l2; simpl; try lia.
  intros. f_equal. apply IHl1. lia.
Qed.

Lemma nth_error_map2 {A B C} (f : A -> B -> C) n l1 l2 x y :
  nth_error l1 n = Some x ->
  nth_error l2 n = Some y ->
  nth_error (map2 f l1 l2) n = Some (f x y).
Proof.
  revert n l2. induction l1; destruct n, l2; simpl; try discriminate; auto.
  intros [= ->] [= ->]. reflexivity.
Qed.

(* Helper: constructor_isprop_pars_decl gives lookup info *)
Lemma constructor_isprop_pars_decl_lookup Σ0 ind c prop npars cdecl :
  EGlobalEnv.constructor_isprop_pars_decl Σ0 ind c = Some (prop, npars, cdecl) ->
  exists mdecl idecl,
    EGlobalEnv.lookup_inductive Σ0 ind = Some (mdecl, idecl) /\
    nth_error (EAst.ind_ctors idecl) c = Some cdecl.
Proof.
  unfold EGlobalEnv.constructor_isprop_pars_decl.
  destruct (EGlobalEnv.lookup_constructor Σ0 ind c) as [[[mdecl0 idecl0] cdecl0]|] eqn:Hlc;
    [|discriminate].
  simpl. intros H.
  assert (cdecl0 = cdecl) by congruence. subst cdecl0.
  destruct (lookup_constructor_decompose _ _ _ _ _ _ Hlc) as [Hl Hn].
  eauto.
Qed.

(* map2_InP reduces to map2 when the function ignores In proofs *)
Lemma map2_InP_gen {A1 A2 B} (l1 : list A1) (l2 : list A2)
  (f : forall (a : A1) (b : A2), In a l1 -> In b l2 -> B) (g : A1 -> A2 -> B) :
  (forall x y (H1 : In x l1) (H2 : In y l2), f x y H1 H2 = g x y) ->
  map2_InP l1 l2 f = map2 g l1 l2.
Proof.
  revert l2 f. induction l1 as [|x xs IH]; intros l2 f Hext.
  - simp map2_InP. reflexivity.
  - destruct l2 as [|y ys].
    + simp map2_InP. reflexivity.
    + simp map2_InP. simpl map2. f_equal.
      * apply Hext.
      * apply IH. intros a b Ha Hb. apply Hext.
Qed.

(* Inverse of nth_error_map2 *)
Lemma nth_error_map2_inv {A B C} (f : A -> B -> C) n l1 l2 z :
  nth_error (map2 f l1 l2) n = Some z ->
  exists x y, nth_error l1 n = Some x /\ nth_error l2 n = Some y /\ z = f x y.
Proof.
  revert n l2. induction l1; destruct n, l2; simpl; try discriminate.
  - intros [= <-]. eauto.
  - exact (IHl1 n l2).
Qed.

(* evaluate_match: skip to the c-th branch *)
Lemma evaluate_match_nth (envM : Sem_env val) (v0 : val) pes err_v bv c pc ec envr :
  nth_error pes c = Some (pc, ec) ->
  (forall i pi ei, i < c -> nth_error pes i = Some (pi, ei) ->
    ALL_DISTINCT_rel conN (pat_bindings pi []) /\
    pmatch (namespace.c val envM) pi v0 [] = No_match env_l) ->
  ALL_DISTINCT_rel conN (pat_bindings pc []) ->
  pmatch (namespace.c val envM) pc v0 [] = Match env_l envr ->
  evaluate {| v := nsAppend (alist_to_ns envr) (namespace.v val envM);
              c := namespace.c val envM |} ec bv ->
  evaluate_match envM v0 pes err_v bv.
Proof.
  revert pes. induction c; intros pes Hnth Hprev Hdist Hmatch Heval.
  - destruct pes as [|[p0 e0] pes']; [discriminate|].
    simpl in Hnth. injection Hnth as -> ->.
    eapply evaluate_match_M; eauto.
  - destruct pes as [|[p0 e0] pes']; [discriminate|].
    destruct (Hprev 0 p0 e0 ltac:(lia) eq_refl) as [Hdist0 Hnm0].
    eapply evaluate_match_NM; eauto.
    eapply IHc.
    + simpl in Hnth. exact Hnth.
    + intros i0 p0' e0' Hi0 Hnth0'. apply (Hprev (S i0) p0' e0'); [lia | exact Hnth0'].
    + exact Hdist.
    + exact Hmatch.
    + exact Heval.
Qed.

(* can_pmatch_all when no pattern gives Match_type_error *)
Lemma can_pmatch_all_forall cenv0 pats v0 :
  (forall p, In p pats -> is_Match_type_error (pmatch cenv0 p v0 []) = false) ->
  can_pmatch_all cenv0 pats v0 = true.
Proof.
  induction pats; simpl; intros; auto.
  rewrite H; [|left; reflexivity].
  apply IHpats. intros p Hin. apply H. right. exact Hin.
Qed.

(* NoDup: distinct elements at different indices *)
Lemma NoDup_nth_error_neq {A} (l : list A) i j (x y : A) :
  List.NoDup l -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> x <> y.
Proof.
  intro Hnd. revert i j. induction Hnd; intros i j Hi Hj Hneq.
  - destruct i; discriminate.
  - destruct i, j; simpl in *; try lia.
    + injection Hi as <-. intros Heq; subst. apply H. eapply nth_error_In. exact Hj.
    + injection Hj as <-. intros Heq; subst. apply H. eapply nth_error_In. exact Hi.
    + eapply IHHnd; [exact Hi | exact Hj | lia].
Qed.

(* pat_bindings_list_helper with Pvar patterns *)
Lemma pat_bindings_list_pvars names acc :
  pat_bindings_list_helper pat_bindings (map Pvar names) acc = List.app (List.rev names) acc.
Proof.
  revert acc. induction names; intros; simpl.
  - reflexivity.
  - rewrite IHnames. simpl. rewrite <- List.app_assoc. reflexivity.
Qed.

(* pat_bindings for Pcon with reversed Pvar patterns *)
Lemma pat_bindings_pcon_pvars_rev cn names :
  pat_bindings (Pcon cn (List.rev (map Pvar names))) [] = names.
Proof.
  simpl. rewrite <- List.map_rev. rewrite pat_bindings_list_pvars.
  rewrite List.rev_involutive. apply List.app_nil_r.
Qed.

(* pmatch: when constructor names differ, result is No_match *)
Lemma pmatch_pcon_no_match cenv0 name_i name_c len_i ps vs env :
  nsLookup _ cenv0 (Short (String.to_string name_i)) =
    Some (len_i, TypeStamp (String.to_string name_i) 0) ->
  #|ps| = len_i ->
  name_i <> name_c ->
  pmatch cenv0 (Pcon (Some (Short (String.to_string name_i))) ps)
    (Conv (Some (TypeStamp (String.to_string name_c) 0)) vs) env = No_match env_l.
Proof.
  intros Hns Hlen Hneq.
  cbn [pmatch]. rewrite Hns.
  replace (same_type (TypeStamp (String.to_string name_c) 0)
                     (TypeStamp (String.to_string name_i) 0))
    with true by reflexivity.
  replace (Nat.eqb (Datatypes.length ps) len_i) with true
    by (symmetry; apply Nat.eqb_eq; exact Hlen).
  simpl andb.
  unfold same_ctor.
  replace (Nat.eqb 0 0) with true by reflexivity.
  simpl andb.
  destruct (Strings.String.eqb_spec (String.to_string name_i) (String.to_string name_c)).
  - exfalso. apply Hneq. apply to_string_injective. exact e.
  - reflexivity.
Qed.

(* pmatch: when constructor names match and patterns are Pvars, result is Match *)
Lemma pmatch_list_helper_pvars cenv0 names vs env :
  #|names| = #|vs| ->
  pmatch_list_helper pmatch cenv0 (List.map Pvar names) vs env =
    Match env_l (List.app (List.rev (map2 pair names vs)) env).
Proof.
  revert vs env. induction names; destruct vs; simpl; intros; try lia.
  - reflexivity.
  - rewrite IHnames by lia. simpl. rewrite <- List.app_assoc. reflexivity.
Qed.

(* pmatch for Pcon with matching name *)
Lemma pmatch_pcon_match cenv0 name len ps vs env :
  nsLookup _ cenv0 (Short (String.to_string name)) =
    Some (len, TypeStamp (String.to_string name) 0) ->
  #|ps| = len ->
  #|vs| = len ->
  pmatch cenv0 (Pcon (Some (Short (String.to_string name))) ps)
    (Conv (Some (TypeStamp (String.to_string name) 0)) vs) env =
    pmatch_list_helper pmatch cenv0 ps vs env.
Proof.
  intros Hns Hplen Hvlen.
  cbn [pmatch]. rewrite Hns.
  replace (same_type (TypeStamp (String.to_string name) 0)
                     (TypeStamp (String.to_string name) 0))
    with true by reflexivity.
  replace (Nat.eqb (Datatypes.length ps) len) with true
    by (symmetry; apply Nat.eqb_eq; exact Hplen).
  simpl andb.
  unfold same_ctor. replace (Nat.eqb 0 0) with true by reflexivity.
  rewrite Strings.String.eqb_refl. simpl andb.
  replace (Nat.eqb (Datatypes.length vs) len) with true
    by (symmetry; apply Nat.eqb_eq; exact Hvlen).
  reflexivity.
Qed.

(* Combined: pmatch for reversed Pvar patterns *)
Lemma pmatch_pcon_pvars_rev_match cenv0 name len names vs :
  nsLookup _ cenv0 (Short (String.to_string name)) =
    Some (len, TypeStamp (String.to_string name) 0) ->
  #|names| = len ->
  #|vs| = len ->
  pmatch cenv0 (Pcon (Some (Short (String.to_string name))) (List.rev (List.map Pvar names)))
    (Conv (Some (TypeStamp (String.to_string name) 0)) vs) [] =
    Match env_l (List.rev (map2 pair (List.rev names) vs)).
Proof.
  intros Hns Hnlen Hvlen.
  rewrite (pmatch_pcon_match _ _ len _ _ _ Hns).
  - rewrite <- List.map_rev. rewrite pmatch_list_helper_pvars.
    + rewrite List.app_nil_r. reflexivity.
    + rewrite List.rev_length. lia.
  - rewrite List.rev_length, List.map_length. lia.
  - exact Hvlen.
Qed.

(* Not type error for Pcon with Pvar sub-patterns *)
Lemma pmatch_pcon_pvars_not_type_error cenv0 name_i name_c len_i names vs :
  nsLookup _ cenv0 (Short (String.to_string name_i)) =
    Some (len_i, TypeStamp (String.to_string name_i) 0) ->
  #|names| = len_i ->
  #|vs| = len_i ->
  is_Match_type_error (pmatch cenv0
    (Pcon (Some (Short (String.to_string name_i))) (List.rev (List.map Pvar names)))
    (Conv (Some (TypeStamp (String.to_string name_c) 0)) vs) []) = false.
Proof.
  intros Hns Hnlen Hvlen.
  cbn [pmatch]. rewrite Hns.
  replace (same_type (TypeStamp (String.to_string name_c) 0)
                     (TypeStamp (String.to_string name_i) 0))
    with true by reflexivity.
  assert (Hplen : #|List.rev (List.map Pvar names)| = len_i)
    by (rewrite List.rev_length, List.map_length; lia).
  replace (Nat.eqb (Datatypes.length (List.rev (List.map Pvar names))) len_i) with true
    by (symmetry; apply Nat.eqb_eq; exact Hplen).
  simpl andb.
  destruct (same_ctor (TypeStamp (String.to_string name_i) 0)
                      (TypeStamp (String.to_string name_c) 0)) eqn:Hsc.
  - replace (Nat.eqb (Datatypes.length vs) len_i) with true
      by (symmetry; apply Nat.eqb_eq; exact Hvlen).
    rewrite <- List.map_rev.
    rewrite pmatch_list_helper_pvars.
    + reflexivity.
    + rewrite List.rev_length. lia.
  - reflexivity.
Qed.

(* Conditional: not type error when name_i = name_c implies #|vs| = len_i *)
Lemma pmatch_pcon_pvars_not_type_error_cond cenv0 name_i name_c len_i names vs :
  nsLookup _ cenv0 (Short (String.to_string name_i)) =
    Some (len_i, TypeStamp (String.to_string name_i) 0) ->
  #|names| = len_i ->
  (name_i = name_c -> #|vs| = len_i) ->
  is_Match_type_error (pmatch cenv0
    (Pcon (Some (Short (String.to_string name_i))) (List.rev (List.map Pvar names)))
    (Conv (Some (TypeStamp (String.to_string name_c) 0)) vs) []) = false.
Proof.
  intros Hns Hnlen Hcond.
  cbn [pmatch]. rewrite Hns.
  replace (same_type (TypeStamp (String.to_string name_c) 0)
                     (TypeStamp (String.to_string name_i) 0))
    with true by reflexivity.
  assert (Hplen : #|List.rev (List.map Pvar names)| = len_i)
    by (rewrite List.rev_length, List.map_length; lia).
  replace (Nat.eqb (Datatypes.length (List.rev (List.map Pvar names))) len_i) with true
    by (symmetry; apply Nat.eqb_eq; exact Hplen).
  simpl andb.
  destruct (same_ctor (TypeStamp (String.to_string name_i) 0)
                      (TypeStamp (String.to_string name_c) 0)) eqn:Hsc.
  - assert (Hne : name_i = name_c).
    { apply to_string_injective. apply Strings.String.eqb_eq.
      unfold same_ctor in Hsc. simpl in Hsc.
      revert Hsc. destruct (Strings.String.eqb (String.to_string name_i) (String.to_string name_c)); auto. }
    specialize (Hcond Hne).
    replace (Nat.eqb (Datatypes.length vs) len_i) with true
      by (symmetry; apply Nat.eqb_eq; exact Hcond).
    rewrite <- List.map_rev.
    rewrite pmatch_list_helper_pvars.
    + reflexivity.
    + rewrite List.rev_length. lia.
  - reflexivity.
Qed.

(* nsAppend / alist_to_ns correspondence with compile_env *)
Lemma nsAppend_alist_compile_env_le1 Σ0 cenv Γ0 nms args :
  #|nms| = #|args| ->
  #|args| <= 1 ->
  {| v := nsAppend (alist_to_ns (List.rev (map2 pair (List.map (fun nm => String.to_string nm) nms) (List.map (compile_value Σ0 cenv) args))))
       (v val (compile_env Σ0 cenv Γ0));
     c := c val (compile_env Σ0 cenv Γ0) |} =
  compile_env Σ0 cenv (add_multiple (List.rev nms) args Γ0).
Proof.
  intros Hlen Hle.
  destruct args as [|a [|? ?]]; destruct nms as [|nm [|? ?]];
    simpl in Hlen; try lia; simpl in Hle; try lia; simpl.
  - unfold compile_env, alist_to_ns, nsAppend. simpl. reflexivity.
  - unfold compile_env, add, alist_to_ns, nsAppend. simpl. reflexivity.
Qed.

(* Main correctness theorem *)
Lemma compile_correct Σ s t Γ cenv :
  ctor_env_ok Σ cenv ->
  cstr_names_distinct Σ ->
  env_ok Σ Γ ->
  wf_term Σ s ->
  wf_globals Σ ->
  consts_val_ok Σ ->
  EWcbvEvalNamed.eval Σ Γ s t ->
  evaluate (compile_env Σ cenv Γ) (compile Σ s) (Rval (compile_value Σ cenv t)) /\ val_ok Σ t.
Proof.
  intros Hctor Hcnd Henv Hwf Hwfg Hcvok Heval.
  revert cenv Hctor Henv Hwf.
  induction Heval using eval_ind; intros cenv Hctor Henv Hwf;
    simp compile; try rewrite <- !compile_equation_1.
  - (* eval_var *)
    split.
    + econstructor.
      rewrite compile_env_lookup. rewrite e. reflexivity.
    + eapply (proj2 Henv). eauto.
  - (* eval_beta *)
    destruct (IHHeval1 cenv Hctor Henv ltac:(inversion Hwf; eassumption)) as [IH1eval IH1ok].
    destruct (IHHeval2 cenv Hctor Henv ltac:(inversion Hwf; eassumption)) as [IH2eval IH2ok].
    assert (Hfr : fresh_name Σ na) by (inversion IH1ok; assumption).
    assert (Hwfb : wf_term Σ b) by (inversion IH1ok; assumption).
    assert (Hcok : consts_ok Σ Γ') by (inversion IH1ok; assumption).
    assert (Hvk : forall na' v0, EWcbvEvalNamed.lookup Γ' na' = Some v0 -> val_ok Σ v0)
      by (inversion IH1ok; assumption).
    assert (Henv' : env_ok Σ (add na a' Γ')).
    { apply env_ok_add; [exact (conj Hcok Hvk) | exact IH2ok | exact Hfr]. }
    destruct (IHHeval3 cenv Hctor Henv' Hwfb) as [IH3eval IH3ok].
    split; [|exact IH3ok].
    eapply evaluate_App with
      (vs := [compile_value Σ cenv a'; compile_value Σ cenv (vClos na b Γ')])
      (env' := compile_env Σ cenv (add na a' Γ'))
      (e := compile Σ b).
    + cbn. econstructor. exact IH2eval. econstructor. exact IH1eval. econstructor.
    + cbn. reflexivity.
    + exact IH3eval.
    + econstructor.
  - (* eval_lambda *)
    split.
    + cbn. econstructor.
    + econstructor;
        [inversion Hwf; assumption | inversion Hwf; assumption | exact (proj1 Henv) | exact (proj2 Henv)].
  - (* eval_zeta *)
    destruct (IHHeval1 cenv Hctor Henv ltac:(inversion Hwf; eassumption)) as [IH1eval IH1ok].
    assert (Hfr : fresh_name Σ (BasicAst.string_of_name (BasicAst.nNamed na)))
      by (inversion Hwf; assumption).
    assert (Henv' : env_ok Σ (add na b0' Γ)).
    { apply env_ok_add; [exact Henv | exact IH1ok | exact Hfr]. }
    destruct (IHHeval2 cenv Hctor Henv' ltac:(inversion Hwf; eassumption)) as [IH2eval IH2ok].
    split; [|exact IH2ok].
    cbn. eapply evaluate_Let.
    + exact IH1eval.
    + cbn.
      change (nsBind (String.to_string na) (compile_value Σ cenv b0') (v val (compile_env Σ cenv Γ)))
        with (v val (compile_env Σ cenv (add na b0' Γ))).
      change (c val (compile_env Σ cenv Γ)) with (c val (compile_env Σ cenv (add na b0' Γ))).
      exact IH2eval.
  - (* eval_iota_block *)
    (* Derive lookup info from constructor_isprop_pars_decl *)
    match goal with H : EGlobalEnv.constructor_isprop_pars_decl _ _ _ = Some _ |- _ =>
      destruct (constructor_isprop_pars_decl_lookup _ _ _ _ _ _ H) as [mdecl [idecl [Hlind Hnth_cdecl]]] end.
    assert (Hnames : lookup_constructor_names Σ ind = Some (map EAst.cstr_name (EAst.ind_ctors idecl)))
      by (unfold lookup_constructor_names; rewrite Hlind; reflexivity).
    (* Wf info *)
    assert (Hwf_discr : wf_term Σ discr) by (inversion Hwf; assumption).
    assert (Hwf_brs : forall binders b, In (binders, b) brs ->
      (forall x, In x binders -> fresh_name Σ (BasicAst.string_of_name x)) /\
      wf_term Σ b /\
      List.NoDup (map (fun x => BasicAst.string_of_name x) binders))
      by (inversion Hwf; assumption).
    assert (Hwf_brs_arity : #|brs| = #|EAst.ind_ctors idecl| /\
      forall i binders0 body cdecl0,
        nth_error brs i = Some (binders0, body) ->
        nth_error (EAst.ind_ctors idecl) i = Some cdecl0 ->
        #|binders0| = EAst.cstr_nargs cdecl0).
    { inversion Hwf; subst.
      match goal with H : context [EGlobalEnv.lookup_inductive _ _ = Some _ -> _] |- _ =>
        specialize (H _ _ Hlind); exact H end. }
    destruct Hwf_brs_arity as [Hbrs_len Hbrs_arity].
    (* IH for discriminant *)
    destruct (IHHeval1 cenv Hctor Henv Hwf_discr) as [IH1eval IH1ok].
    assert (Hargs_ok : forall v0, In v0 args -> val_ok Σ v0) by (inversion IH1ok; assumption).
    assert (Hargs_le1 : #|args| <= 1) by (inversion IH1ok; assumption).
    (* Branch info *)
    assert (Hbr_in : In br brs) by (eapply nth_error_In; eassumption).
    destruct br as [br_binders br_body].
    simpl fst in *. simpl snd in *.
    destruct (Hwf_brs br_binders br_body Hbr_in) as [Hfresh_binders [Hwf_body Hnodup_binders]].
    match goal with H : Forall2 _ br_binders nms |- _ => rename H into HF2_brs end.
    assert (Hnms_len : #|nms| = #|args|).
    { match goal with H : #|args| = #|br_binders| |- _ => rewrite H end.
      symmetry. exact (Forall2_length' HF2_brs). }
    assert (Hfresh_nms : forall nm, In nm nms -> fresh_name Σ nm).
    { clear -HF2_brs Hfresh_binders; revert Hfresh_binders; induction HF2_brs as [|x y xs ys Hxy HF IH];
          intros Hfresh_binders nm Hin; [destruct Hin|].
      destruct Hin as [<-|Hin].
      - specialize (Hfresh_binders x (or_introl eq_refl)). rewrite Hxy in Hfresh_binders. exact Hfresh_binders.
      - apply IH; [|exact Hin]. intros x0 Hx0. apply Hfresh_binders. right. exact Hx0. }
    (* env_ok for branch body *)
    assert (Henv_body : env_ok Σ (add_multiple (List.rev nms) args Γ)).
    { destruct args as [|a [|? ?]]; destruct nms as [|nm [|? ?]];
        simpl in Hnms_len; try lia; simpl in Hargs_le1; try lia; simpl.
      - exact Henv.
      - apply env_ok_add; [exact Henv | apply Hargs_ok; left; reflexivity | apply Hfresh_nms; left; reflexivity]. }
    destruct (IHHeval2 cenv Hctor Henv_body Hwf_body) as [IH2eval IH2ok].
    assert (Hnth_name : nth_error (map EAst.cstr_name (EAst.ind_ctors idecl)) c = Some (EAst.cstr_name cdecl))
      by (exact (nth_error_map_In _ _ _ _ Hnth_cdecl)).
    assert (Hns : nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl))) =
      Some (EAst.cstr_nargs cdecl, TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0))
      by (eapply Hctor; eauto).
    split; [|exact IH2ok].
    (* Compile reduces to Mat *)
    simp compile. rewrite Hnames.
    rewrite (map2_InP_gen _ _ _
      (fun name br => let '(binders, body) := br in
        (Pcon (Some (Short (String.to_string name)))
          (rev (map (fun x => Pvar (String.to_string (BasicAst.string_of_name x))) binders)),
         compile Σ body)));
      [| intros; destruct y as [? ?]; reflexivity].
    set (compiled_brs := map2 _ _ brs).
    (* Get nth_error brs c *)
    match goal with Hn : nth_error brs c = Some (br_binders, br_body) |- _ =>
      rename Hn into Hnth_brs_c end.
    (* nth_error compiled_brs c *)
    assert (Hnth_cb : nth_error compiled_brs c = Some
      (Pcon (Some (Short (String.to_string (EAst.cstr_name cdecl))))
        (rev (map (fun x => Pvar (String.to_string (BasicAst.string_of_name x))) br_binders)),
       compile Σ br_body)).
    { unfold compiled_brs. exact (nth_error_map2 _ _ _ _ _ _ Hnth_name Hnth_brs_c). }
    (* NoDup on constructor names *)
    assert (Hnd_cnames : List.NoDup (map EAst.cstr_name (EAst.ind_ctors idecl)))
      by (exact (Hcnd _ _ _ Hlind)).
    (* #|args| = cstr_nargs cdecl *)
    match goal with H : #|args| = EAst.cstr_nargs cdecl |- _ =>
      rename H into Hargs_arity end.
    (* Convert pattern names from br_binders to nms *)
    assert (Hpat_names : map (fun x => String.to_string (BasicAst.string_of_name x)) br_binders = map String.to_string nms).
    { clear -HF2_brs; induction HF2_brs as [|x0 y0 xs0 ys0 Hxy HF2' IH]; simpl.
      - reflexivity.
      - subst. simpl. rewrite IH. reflexivity. }
    eapply evaluate_Mat.
    + exact IH1eval.
    + (* evaluate_match *)
      rewrite (compile_value_construct _ _ _ _ _ _ _ Hnames Hnth_name).
      change (namespace.c val (compile_env Σ cenv Γ)) with cenv.
      eapply (evaluate_match_nth _ _ _ _ _ c).
      * exact Hnth_cb.
      * (* For i < c: ALL_DISTINCT and No_match *)
        intros i pi ei Hi Hnth_cb_i.
        unfold compiled_brs in Hnth_cb_i.
        destruct (nth_error_map2_inv _ _ _ _ _ Hnth_cb_i) as [name_i [[binders_i body_i] [Hnth_name_i [Hnth_brs_i Heq_i]]]].
        injection Heq_i as Heq_pi Heq_ei. subst pi ei.
        (* Get cdecl_i *)
        destruct (nth_error_map_inv _ _ _ _ Hnth_name_i) as [cdecl_i [Hnth_cdecl_i Hname_eq_i]].
        subst name_i.
        split.
        -- (* ALL_DISTINCT *)
           apply NoDup_ALL_DISTINCT_rel.
           rewrite <- List.map_map. rewrite rev_is_List_rev.
           rewrite pat_bindings_pcon_pvars_rev.
           rewrite <- List.map_map.
           apply NoDup_map_injective; [exact to_string_injective|].
           destruct (Hwf_brs binders_i body_i (nth_error_In _ _ Hnth_brs_i)) as [_ [_ Hnd_i]].
           exact Hnd_i.
        -- (* No_match *)
           assert (Hns_i : nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl_i))) =
             Some (EAst.cstr_nargs cdecl_i, TypeStamp (String.to_string (EAst.cstr_name cdecl_i)) 0))
             by (eapply Hctor; eauto).
           assert (Hlen_ps : #|rev (map (fun x => Pvar (String.to_string (BasicAst.string_of_name x))) binders_i)| = EAst.cstr_nargs cdecl_i).
           { rewrite rev_is_List_rev, List.rev_length, List.map_length.
             exact (Hbrs_arity i binders_i body_i cdecl_i Hnth_brs_i Hnth_cdecl_i). }
           assert (Hneq_name : EAst.cstr_name cdecl_i <> EAst.cstr_name cdecl).
           { eapply (NoDup_nth_error_neq _ i c); [exact Hnd_cnames| | |lia].
             - exact (nth_error_map_In _ _ _ _ Hnth_cdecl_i).
             - exact Hnth_name. }
           exact (pmatch_pcon_no_match _ _ _ _ _ _ _ Hns_i Hlen_ps Hneq_name).
      * (* ALL_DISTINCT for c-th branch *)
        apply NoDup_ALL_DISTINCT_rel.
        rewrite <- List.map_map. rewrite rev_is_List_rev.
        rewrite pat_bindings_pcon_pvars_rev.
        rewrite <- List.map_map.
        apply NoDup_map_injective; [exact to_string_injective|].
        exact Hnodup_binders.
      * (* pmatch at c gives Match *)
        rewrite <- (List.map_map (fun x => String.to_string (BasicAst.string_of_name x)) Pvar br_binders).
        rewrite Hpat_names. rewrite rev_is_List_rev.
        exact (pmatch_pcon_pvars_rev_match _ _ (EAst.cstr_nargs cdecl) _ _ Hns
          (eq_trans (map_length String.to_string nms) (eq_trans Hnms_len Hargs_arity))
          (eq_trans (map_length (compile_value Σ cenv) args) Hargs_arity)).
      * (* Body evaluates *)
        assert (Hrev_snms : List.rev (map String.to_string nms) = map String.to_string nms).
        { destruct nms as [|nm0 [|? ?]]; [reflexivity|reflexivity|].
          exfalso. simpl in Hnms_len. simpl in Hargs_le1. lia. }
        rewrite Hrev_snms.
        change cenv with (namespace.c val (compile_env Σ cenv Γ)).
        rewrite nsAppend_alist_compile_env_le1.
        -- exact IH2eval.
        -- exact Hnms_len.
        -- exact Hargs_le1.
    + (* can_pmatch_all *)
      rewrite (compile_value_construct _ _ _ _ _ _ _ Hnames Hnth_name).
      change (namespace.c val (compile_env Σ cenv Γ)) with cenv.
      apply can_pmatch_all_forall.
      intros p Hp.
      (* p is in map fst compiled_brs *)
      apply in_map_iff in Hp.
      destruct Hp as [pe [Hfst Hpe]]. subst p.
      unfold compiled_brs in Hpe.
      apply In_map2_idx in Hpe.
      destruct Hpe as [i [name_i [[binders_i body_i] [Hnth_name_i [Hnth_brs_i Heq_pe]]]]].
      subst pe. simpl fst.
      (* Get cdecl_i *)
      destruct (nth_error_map_inv _ _ _ _ Hnth_name_i) as [cdecl_i [Hnth_cdecl_i Hname_eq_i]].
      subst name_i.
      (* nsLookup *)
      assert (Hns_i : nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl_i))) =
        Some (EAst.cstr_nargs cdecl_i, TypeStamp (String.to_string (EAst.cstr_name cdecl_i)) 0))
        by (eapply Hctor; eauto).
      (* Branch arity *)
      assert (Harity_i : #|binders_i| = EAst.cstr_nargs cdecl_i)
        by (exact (Hbrs_arity i binders_i body_i cdecl_i Hnth_brs_i Hnth_cdecl_i)).
      (* Convert pattern form *)
      rewrite <- (List.map_map (fun x => String.to_string (BasicAst.string_of_name x)) Pvar binders_i).
      rewrite rev_is_List_rev.
      (* Apply conditional not_type_error *)
      apply (pmatch_pcon_pvars_not_type_error_cond _ _ (EAst.cstr_name cdecl) (EAst.cstr_nargs cdecl_i)
        (map (fun x => String.to_string (BasicAst.string_of_name x)) binders_i)
        (map (compile_value Σ cenv) args)).
      * exact Hns_i.
      * rewrite List.map_length. exact Harity_i.
      * intro Hname_eq.
        (* name_i = name_c → i = c → cdecl_i = cdecl *)
        assert (Hi_eq_c : i = c).
        { destruct (Nat.eq_dec i c) as [|Hne]; [assumption|exfalso].
          eapply (NoDup_nth_error_neq _ i c _ _ Hnd_cnames
            (nth_error_map_In _ _ _ _ Hnth_cdecl_i) (nth_error_map_In _ _ _ _ Hnth_cdecl) Hne).
          exact Hname_eq. }
        subst i.
        assert (cdecl_i = cdecl) by congruence. subst cdecl_i.
        rewrite List.map_length. lia.
  - (* eval_fix_unfold *)
    destruct (IHHeval1 cenv Hctor Henv ltac:(inversion Hwf; eassumption)) as [IH1eval IH1ok].
    destruct (IHHeval3 cenv Hctor Henv ltac:(inversion Hwf; eassumption)) as [IH3eval IH3ok].
    (* Extract info from val_ok of vRecClos *)
    assert (Hmfix_ok : forall n b, In (n, b) mfix -> fresh_name Σ n /\ wf_term Σ b)
      by (inversion IH1ok; assumption).
    assert (Hcok : consts_ok Σ Γ') by (inversion IH1ok; assumption).
    assert (Hvk : forall na0 v0, EWcbvEvalNamed.lookup Γ' na0 = Some v0 -> val_ok Σ v0)
      by (inversion IH1ok; assumption).
    assert (Hmfix_len1 : #|mfix| <= 1) by (inversion IH1ok; assumption).
    (* Restrict to singleton mfix *)
    assert (Hmfix_ge1 : idx < #|mfix|).
    { match goal with H : nth_error mfix idx = Some _ |- _ =>
        apply nth_error_Some; congruence end. }
    assert (Hmfix_eq1 : #|mfix| = 1) by lia.
    assert (Hidx0 : idx = 0) by lia. subst idx.
    destruct mfix as [|[na0 body0] []]; simpl in Hmfix_eq1; try lia.
    match goal with H : nth_error _ _ = Some _ |- _ =>
      simpl in H; injection H as -> -> end.
    (* Now mfix = [(na', tLambda (nNamed na) fn)] *)
    (* Get wf info for body *)
    assert (Hwf_body : wf_term Σ (EAst.tLambda (BasicAst.nNamed na) fn)).
    { specialize (Hmfix_ok _ _ (or_introl eq_refl)) as [? ?]; auto. }
    assert (Hfr_na' : fresh_name Σ na').
    { specialize (Hmfix_ok _ _ (or_introl eq_refl)) as [? ?]; auto. }
    assert (Hfr_na : fresh_name Σ na) by (inversion Hwf_body; assumption).
    assert (Hwf_fn : wf_term Σ fn) by (inversion Hwf_body; assumption).
    (* Build env_ok for the body environment *)
    assert (Henv_Γ' : env_ok Σ Γ') by exact (conj Hcok Hvk).
    assert (Hvok_rec : val_ok Σ (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ')).
    { econstructor; [exact Hmfix_ok | exact Hcok | exact Hvk | simpl; lia]. }
    assert (Henv1 : env_ok Σ (add na' (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ') Γ')).
    { apply env_ok_add; [exact Henv_Γ' | exact Hvok_rec | exact Hfr_na']. }
    assert (Henv2 : env_ok Σ (add na av (add na' (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ') Γ'))).
    { apply env_ok_add; [exact Henv1 | exact IH3ok | exact Hfr_na]. }
    (* Simplify the extended environment *)
    change (fix_env [(na', EAst.tLambda (BasicAst.nNamed na) fn)] Γ')
      with [vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ'] in *.
    simpl List.rev in *. simpl map in *. simpl add_multiple in *.
    (* Get IH for body evaluation *)
    destruct (IHHeval2 cenv Hctor Henv2 Hwf_fn) as [IH2eval IH2ok].
    split; [|exact IH2ok].
    simp compile.
    eapply evaluate_App with
      (vs := [compile_value Σ cenv av;
              compile_value Σ cenv (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ')])
      (env' := compile_env Σ cenv
                 (add na av (add na' (vRecClos [(na', EAst.tLambda (BasicAst.nNamed na) fn)] 0 Γ') Γ')))
      (e := compile Σ fn).
    + cbn. econstructor. exact IH3eval. econstructor. exact IH1eval. econstructor.
    + apply do_opapp_fix_unfold.
    + exact IH2eval.
    + econstructor.
  - (* eval_fix *)
    simp compile. rewrite map_InP_spec.
    set (bodies := List.map _ mfix).
    set (mfix' := map2 (fun n d => (n, EAst.dbody d)) nms mfix).
    assert (Hbodies_eq : bodies =
      List.map (fun '(recn, b) => let '(arg, expr) := force_lambda (compile Σ b) in
        (String.to_string recn, arg, expr)) mfix').
    { unfold bodies, mfix'. apply compile_fix_bodies. exact f6. }
    assert (Hmfix_len1 : #|mfix| = 1) by (inversion Hwf; lia).
    assert (Hidx0 : idx = 0) by lia. subst idx.
    destruct mfix as [|d []]; simpl in Hmfix_len1; try lia.
    assert (Hnms_len : #|nms| = 1) by (apply Forall2_length' in f6; simpl in f6; lia).
    destruct nms as [|nm []]; simpl in Hnms_len; try lia.
    inversion f6; subst. inversion H4; subst.
    assert (Hname_d : BasicAst.string_of_name (EAst.dname d) = nm).
    { match goal with H : BasicAst.nNamed _ = EAst.dname d |- _ =>
        rewrite <- H; reflexivity end. }
    subst mfix'.
    split.
    + rewrite Hbodies_eq. simpl map2. simpl List.map.
      destruct (force_lambda (compile Σ (EAst.dbody d))) as [an be] eqn:Hfl.
      rewrite (compile_value_RecClos_singleton _ _ _ _ _ _ _ Hfl).
      simpl.
      eapply evaluate_Letrec.
      * apply NoDup_ALL_DISTINCT_rel. constructor; [intros [] | constructor].
      * apply evaluate_Var_singleton_rec.
    + (* val_ok *)
      simpl map2.
      econstructor.
      * intros n0 b0 Hin. simpl in Hin.
        destruct Hin as [Heq | []].
        inversion Heq; subst.
        inversion Hwf; subst.
        match goal with H : forall _, In _ _ -> _ |- _ =>
          specialize (H d ltac:(left; reflexivity)) as [Hfr Hwfb] end.
        match goal with H : BasicAst.nNamed _ = EAst.dname d |- _ =>
          rewrite <- H in Hfr; simpl in Hfr end.
        split; [exact Hfr | exact Hwfb].
      * exact (proj1 Henv).
      * exact (proj2 Henv).
      * simpl. lia.
  - (* eval_delta *)
    split.
    + econstructor. rewrite compile_env_lookup.
      assert (Htmp : EWcbvEvalNamed.lookup Γ (Kernames.string_of_kername c) = Some res).
      { eapply (proj1 Henv); eauto. }
      rewrite Htmp. reflexivity.
    + eapply Hcvok; eauto.
  - (* eval_construct_block *)
    destruct (lookup_constructor_decompose _ _ _ _ _ _ e) as [Hlind Hnth].
    assert (Harity : #|args| = EAst.cstr_nargs cdecl).
    { inversion Hwf; subst; match goal with H : forall _ _ _, _ = Some _ -> _ |- _ => eapply H; eauto end. }
    assert (Harity_le : #|args| <= 1).
    { inversion Hwf; assumption. }
    assert (Hnames : lookup_constructor_names Σ ind = Some (map EAst.cstr_name (EAst.ind_ctors idecl))).
    { unfold lookup_constructor_names. rewrite Hlind. reflexivity. }
    assert (Hnth_name : nth_error (map EAst.cstr_name (EAst.ind_ctors idecl)) c = Some (EAst.cstr_name cdecl)).
    { exact (nth_error_map_In EAst.cstr_name c (EAst.ind_ctors idecl) cdecl Hnth). }
    assert (Hns : nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl))) =
      Some (EAst.cstr_nargs cdecl, TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0)).
    { eapply Hctor; eauto. }
    assert (Hname_eq : nth c (map EAst.cstr_name (EAst.ind_ctors idecl)) ""%bs = EAst.cstr_name cdecl).
    { exact (nth_error_nth_default c _ _ _ Hnth_name). }
    assert (Hwf_args : forall t, In t args -> wf_term Σ t) by (inversion Hwf; assumption).
    destruct (compile_All2_evaluate_list Σ cenv Γ args args' a Hctor Henv Hwf_args Hwfg Hcvok IHa)
      as [Heval_list Hvok].
    assert (Hargs'_le : #|args'| <= 1).
    { enough (Hlen : #|args| = #|args'|) by lia.
      clear -a. depind a; simpl; auto; lia. }
    split.
    + rewrite Hnames. rewrite map_InP_spec.
      rewrite (compile_value_construct _ _ _ _ args' _ _ Hnames Hnth_name).
      rewrite Hname_eq.
      assert (Hdc : do_con_check cenv (Some (Short (String.to_string (EAst.cstr_name cdecl)))) #|List.map (compile Σ) args| = true).
      { unfold do_con_check. rewrite Hns. rewrite map_length. rewrite Harity. apply Nat.eqb_refl. }
      assert (Hbc : build_conv cenv (Some (Short (String.to_string (EAst.cstr_name cdecl))))
        (List.map (compile_value Σ cenv) args') =
        Some (Conv (Some (TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0)) (List.map (compile_value Σ cenv) args'))).
      { unfold build_conv. rewrite Hns. reflexivity. }
      eapply evaluate_Con with (vs := rev (List.map (compile_value Σ cenv) args')).
      * exact Hdc.
      * change (namespace.c val (compile_env Σ cenv Γ)) with cenv.
        rewrite <- rev_is_List_rev, rev_rev. exact Hbc.
      * rewrite <- rev_is_List_rev. exact Heval_list.
    + constructor; assumption.
  - (* eval_construct_block_empty *)
    destruct (lookup_constructor_decompose _ _ _ _ _ _ e) as [Hlind Hnth].
    assert (Harity : 0 = EAst.cstr_nargs cdecl).
    { inversion Hwf; subst; match goal with H : forall _ _ _, _ = Some _ -> _ |- _ => eapply H; eauto end. }
    assert (Hnames : lookup_constructor_names Σ ind = Some (map EAst.cstr_name (EAst.ind_ctors idecl))).
    { unfold lookup_constructor_names. rewrite Hlind. reflexivity. }
    assert (Hnth_name : nth_error (map EAst.cstr_name (EAst.ind_ctors idecl)) c = Some (EAst.cstr_name cdecl)).
    { exact (nth_error_map_In EAst.cstr_name c (EAst.ind_ctors idecl) cdecl Hnth). }
    assert (Hns : nsLookup _ cenv (Short (String.to_string (EAst.cstr_name cdecl))) =
      Some (EAst.cstr_nargs cdecl, TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0)).
    { eapply Hctor; eauto. }
    assert (Hname_eq : nth c (map EAst.cstr_name (EAst.ind_ctors idecl)) ""%bs = EAst.cstr_name cdecl).
    { exact (nth_error_nth_default c _ _ _ Hnth_name). }
    split.
    + rewrite Hnames. simp map_InP.
      rewrite (compile_value_construct _ _ _ _ [] _ _ Hnames Hnth_name). cbn [map].
      rewrite Hname_eq.
      assert (Hdc : do_con_check cenv (Some (Short (String.to_string (EAst.cstr_name cdecl)))) 0 = true).
      { unfold do_con_check. rewrite Hns. simpl. rewrite <- Harity. reflexivity. }
      assert (Hbc : build_conv cenv (Some (Short (String.to_string (EAst.cstr_name cdecl)))) [] =
        Some (Conv (Some (TypeStamp (String.to_string (EAst.cstr_name cdecl)) 0)) [])).
      { unfold build_conv. rewrite Hns. reflexivity. }
      eapply evaluate_Con with (vs := []).
      * exact Hdc.
      * exact Hbc.
      * exact (evaluate_nil _).
    + constructor. intros v0 Hv0. destruct Hv0. simpl. lia.
  - (* eval_prim *)
    exfalso. inversion Hwf.
  - (* eval_lazy *)
    exfalso. inversion Hwf.
  - (* eval_force *)
    exfalso. inversion Hwf.
Qed.
