From Stdlib Require Import List Lia DecimalNat.
From Stdlib Require Strings.String.
Import ListNotations.
From MetaRocq.Utils Require Import utils ReflectEq bytestring MRList MRString.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed EPrimitive ELiftSubst.
From MetaRocq.Erasure Require Import EWcbvEvalNamed.
From Equations Require Import Equations.
From CakeML Require Import ast namespace semanticPrimitives functions bigstep.
From CakeML Require Import Compile.
From CakeML.CakeML.proofs Require Import helper_lemmas determinism.

Set Default Goal Selector "!".

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

Lemma to_string_injective (x y : bytestring.string) :
  String.to_string x = String.to_string y -> x = y.
Proof.
  intros H. apply (f_equal String.of_string) in H.
  now rewrite !of_string_to_string in H.
Qed.

Lemma local_name_inj x y : local_name x = local_name y -> x = y.
Proof.
  unfold local_name. intros H. apply to_string_injective in H.
  now injection H.
Qed.

Lemma local_global_name x Σ kn : local_name x <> global_name Σ kn.
Proof.
  unfold local_name, global_name, global_ident, global_ident_at. cbn. congruence.
Qed.

Fixpoint no_us (s : bytestring.string) : Prop :=
  match s with
  | String.EmptyString => True
  | String.String b s => b <> "_"%byte /\ no_us s
  end.

Lemma no_us_string_of_uint u : no_us (string_of_uint u).
Proof. induction u; cbn; split; auto; discriminate. Qed.

Lemma string_of_uint_inj u1 u2 : string_of_uint u1 = string_of_uint u2 -> u1 = u2.
Proof.
  induction u1 in u2 |- *; destruct u2; cbn; intros H; try discriminate;
    try reflexivity; injection H as H; f_equal; auto.
Qed.

Lemma string_of_nat_inj n m : string_of_nat n = string_of_nat m -> n = m.
Proof.
  unfold string_of_nat. intros H. apply string_of_uint_inj in H.
  rewrite <- (DecimalNat.Unsigned.of_to n), <- (DecimalNat.Unsigned.of_to m). now rewrite H.
Qed.

Lemma split_us a b x y :
  no_us a -> no_us b ->
  (a ++ String.String "_"%byte x = b ++ String.String "_"%byte y)%bs -> a = b /\ x = y.
Proof.
  induction a in b |- *; destruct b; cbn.
  - intros _ _ H. now injection H.
  - intros _ [Hb _] H. injection H as <- _. congruence.
  - intros [Ha _] _ H. injection H as -> _. congruence.
  - intros [_ Ha] [_ Hb] H. injection H as <- H.
    destruct (IHa _ Ha Hb H). now subst.
Qed.

Lemma ctor_name_inj c1 d1 c2 d2 :
  ctor_name c1 d1 = ctor_name c2 d2 -> c1 = c2 /\ cstr_nargs d1 = cstr_nargs d2.
Proof.
  unfold ctor_name, ctor_ident. intros H. apply to_string_injective in H.
  cbn in H. injection H as H.
  apply split_us in H as [H1 H]; try apply no_us_string_of_uint.
  apply split_us in H as [H2 _]; try apply no_us_string_of_uint.
  split; now apply string_of_nat_inj.
Qed.

Definition ctor_entries (Σ : global_declarations) : list (String.string * (nat * stamp)) :=
  flat_map (fun '(kn, d) =>
    match d with
    | InductiveDecl mib =>
        flat_map (fun idecl =>
          mapi (fun c cdecl => (ctor_name c cdecl, (cstr_nargs cdecl, TypeStamp (ctor_name c cdecl) 0)))
            idecl.(ind_ctors)) mib.(ind_bodies)
    | ConstantDecl _ => []
    end) Σ.

Definition ctor_env (Σ : global_declarations) : env_ctor :=
  Bind modN conN (nat * stamp) (ctor_entries Σ) [].

Lemma ALOOKUP_uniform {A} (l : list (String.string * A)) k v :
  In (k, v) l ->
  (forall v', In (k, v') l -> v' = v) ->
  ALOOKUP A l k = Some v.
Proof.
  induction l as [|[k' v'] l IH]; cbn; [intros []|].
  intros Hin Huni.
  destruct (Strings.String.eqb_spec k' k) as [->|Hne].
  - f_equal. apply Huni. now left.
  - destruct Hin as [[= -> ->]|Hin]; [congruence|].
    apply IH; auto.
Qed.

Lemma In_mapi_rec_nth {A B} (f : nat -> A -> B) l k c x :
  nth_error l c = Some x -> In (f (k + c) x) (mapi_rec f l k).
Proof.
  induction l in k, c |- *; destruct c; cbn; try discriminate.
  - intros [= ->]. rewrite Nat.add_0_r. now left.
  - intros H. right. rewrite Nat.add_succ_r, <- Nat.add_succ_l. now apply IHl.
Qed.

Lemma In_mapi_nth {A B} (f : nat -> A -> B) l c x :
  nth_error l c = Some x -> In (f c x) (mapi f l).
Proof. apply (In_mapi_rec_nth f l 0). Qed.

Lemma In_mapi_rec_inv {A B} (f : nat -> A -> B) l k y :
  In y (mapi_rec f l k) -> exists c x, nth_error l c = Some x /\ y = f (k + c) x.
Proof.
  induction l in k |- *; cbn; [intros []|].
  intros [<-|Hin].
  - exists 0, a. now rewrite Nat.add_0_r.
  - destruct (IHl _ Hin) as (c & x & Hn & ->). exists (S c), x.
    split; [exact Hn|]. now rewrite Nat.add_succ_r.
Qed.

Lemma In_mapi_inv {A B} (f : nat -> A -> B) l y :
  In y (mapi f l) -> exists c x, nth_error l c = Some x /\ y = f c x.
Proof. apply (In_mapi_rec_inv f l 0). Qed.

Lemma lookup_env_In' Σ kn d :
  lookup_env Σ kn = Some d -> In (kn, d) Σ.
Proof.
  induction Σ as [|[kn' d'] Σ IH]; cbn; [discriminate|].
  destruct (eqb_spec kn kn') as [->|].
  - intros [= ->]. now left.
  - intros Hl. right. auto.
Qed.

Lemma lookup_inductive_In Σ ind mdecl idecl :
  lookup_inductive Σ ind = Some (mdecl, idecl) ->
  In (inductive_mind ind, InductiveDecl mdecl) Σ /\ In idecl mdecl.(ind_bodies).
Proof.
  unfold lookup_inductive, lookup_minductive.
  destruct lookup_env as [[|mdecl']|] eqn:He; cbn; try discriminate.
  destruct nth_error eqn:Hn; cbn; try discriminate.
  intros [= -> ->]. split.
  - now apply lookup_env_In'.
  - now eapply nth_error_In.
Qed.

Lemma ctor_env_lookup Σ ind mdecl idecl c cdecl :
  lookup_inductive Σ ind = Some (mdecl, idecl) ->
  nth_error idecl.(ind_ctors) c = Some cdecl ->
  nsLookup (nat * stamp) (ctor_env Σ) (Short (ctor_name c cdecl)) =
    Some (cstr_nargs cdecl, TypeStamp (ctor_name c cdecl) 0).
Proof.
  intros Hl Hc. cbn. apply lookup_inductive_In in Hl as [Hm Hi].
  apply ALOOKUP_uniform.
  - unfold ctor_entries. eapply in_flat_map. eexists; split; [exact Hm|]. cbn.
    eapply in_flat_map. eexists; split; [exact Hi|].
    eapply (In_mapi_nth (fun c cdecl => (ctor_name c cdecl, (cstr_nargs cdecl, TypeStamp (ctor_name c cdecl) 0)))).
    exact Hc.
  - intros v' Hin. unfold ctor_entries in Hin.
    apply in_flat_map in Hin as ([kn d] & _ & Hin).
    destruct d as [|mib]; [destruct Hin|].
    apply in_flat_map in Hin as (idecl' & _ & Hin).
    apply In_mapi_inv in Hin as (c' & cdecl' & _ & Heq).
    pose proof (f_equal fst Heq) as Hname; cbn [fst] in Hname.
    pose proof (f_equal snd Heq) as Hv; cbn [snd] in Hv.
    pose proof (ctor_name_inj _ _ _ _ Hname) as [_ Hn].
    now rewrite Hv, Hname, Hn.
Qed.

Lemma ALOOKUP_app {A} (l1 l2 : list (String.string * A)) k :
  ALOOKUP A (l1 ++ l2) k =
    match ALOOKUP A l1 k with Some x => Some x | None => ALOOKUP A l2 k end.
Proof.
  induction l1 as [|[k' v'] l1 IH]; cbn; [reflexivity|].
  destruct Strings.String.eqb; auto.
Qed.

Lemma ALOOKUP_notin {A} (l : list (String.string * A)) k :
  ~ In k (map fst l) -> ALOOKUP A l k = None.
Proof.
  induction l as [|[k' v'] l IH]; cbn; [reflexivity|].
  intros Hn. destruct (Strings.String.eqb_spec k' k); [tauto|].
  apply IH. tauto.
Qed.

Lemma ALOOKUP_NoDup {A} (l : list (String.string * A)) k v :
  NoDup (map fst l) -> In (k, v) l -> ALOOKUP A l k = Some v.
Proof.
  intros Hnd Hin. apply ALOOKUP_uniform; [exact Hin|].
  induction l as [|[k' v'] l IH]; cbn in *; [tauto|].
  inversion Hnd as [|? ? Hni Hnd']; subst.
  intros v'' [[= <- <-]|Hin''].
  - destruct Hin as [[= <-]|Hin]; [reflexivity|].
    exfalso. apply Hni. now apply (in_map fst) in Hin.
  - destruct Hin as [[= -> ->]|Hin].
    + exfalso. apply Hni. now apply (in_map fst) in Hin''.
    + now apply IH.
Qed.

Lemma nsLookup_Bind {A} (l : list (String.string * A)) m k :
  nsLookup A (Bind modN varN A l m) (Short k) = ALOOKUP A l k.
Proof. reflexivity. Qed.

Lemma nsLookup_nsBind k w (ns : namespace modN varN val) k' :
  nsLookup val (nsBind k w ns) (Short k') =
    if Strings.String.eqb k k' then Some w else nsLookup val ns (Short k').
Proof. now destruct ns. Qed.

Lemma lookup_add a w Γ na :
  EWcbvEvalNamed.lookup (add a w Γ) na = if na == a then Some w else EWcbvEvalNamed.lookup Γ na.
Proof.
  unfold add, EWcbvEvalNamed.lookup. cbn. change (String.eqb na a) with (na == a).
  destruct (na == a); reflexivity.
Qed.

Lemma lookup_add_multiple_inv ks vs Γ y v :
  #|ks| = #|vs| ->
  EWcbvEvalNamed.lookup (add_multiple ks vs Γ) y = Some v ->
  (exists i, nth_error ks i = Some y /\ nth_error vs i = Some v) \/
  (~ In y ks /\ EWcbvEvalNamed.lookup Γ y = Some v).
Proof.
  induction ks in vs |- *; destruct vs; cbn; try discriminate; intros Hlen.
  - intros H. right. auto.
  - rewrite lookup_add. destruct (eqb_spec y a) as [->|Hne].
    + intros [= ->]. left. now exists 0.
    + intros H. destruct (IHks vs ltac:(lia) H) as [(i & H1 & H2)|[Hn H']].
      * left. now exists (S i).
      * right. split; auto. intros [->|]; auto.
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

Lemma fix_env_length mfix Γ : #|fix_env mfix Γ| = #|mfix|.
Proof.
  unfold fix_env. induction #|mfix|; cbn; lia.
Qed.

Lemma lookup_fix_env mfix Γ' Γ y v :
  EWcbvEvalNamed.lookup (add_multiple (List.rev (map fst mfix)) (fix_env mfix Γ') Γ) y = Some v ->
  (exists j, nth_error (map fst mfix) j = Some y /\ v = vRecClos mfix j Γ') \/
  (~ In y (map fst mfix) /\ EWcbvEvalNamed.lookup Γ y = Some v).
Proof.
  intros H. apply lookup_add_multiple_inv in H as [(i & H1 & H2)|[Hn H']].
  - left. assert (Hi : i < #|mfix|).
    { apply nth_error_Some_length in H1. now rewrite List.length_rev, List.length_map in H1. }
    rewrite nth_error_fix_env in H2 by exact Hi. injection H2 as <-.
    exists (#|mfix| - S i). split; [|reflexivity].
    rewrite nth_error_rev in H1 by (now rewrite List.length_rev, List.length_map).
    now rewrite List.rev_involutive, List.length_rev, List.length_map in H1.
  - right. split; auto. intros Hin. apply Hn. rewrite <- List.in_rev. exact Hin.
  - now rewrite List.length_rev, List.length_map, fix_env_length.
Qed.

Lemma declared_constant_inj Σ kn d1 d2 :
  declared_constant Σ kn d1 -> declared_constant Σ kn d2 -> d1 = d2.
Proof. unfold declared_constant. congruence. Qed.

Section Correctness.
  Context (Σ : global_declarations).

  Inductive wf : term -> Prop :=
  | wf_tBox : wf tBox
  | wf_tRel n : wf (tRel n)
  | wf_tVar na : wf (tVar na)
  | wf_tEvar n l : wf (tEvar n l)
  | wf_tLambda nm b : wf b -> wf (tLambda nm b)
  | wf_tLetIn nm d b : wf d -> wf b -> wf (tLetIn nm d b)
  | wf_tApp f a : wf f -> wf a -> wf (tApp f a)
  | wf_tConst c : wf (tConst c)
  | wf_tConstruct ind c args :
      (forall mdecl idecl cdecl, lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
         #|args| = cstr_nargs cdecl) ->
      Forall wf args ->
      wf (tConstruct ind c args)
  | wf_tCase ind mch brs : wf mch -> Forall (fun br => wf br.2) brs -> wf (tCase ind mch brs)
  | wf_tProj p t : wf (tProj p t)
  | wf_tFix mfix idx : Forall (fun d => wf d.(dbody)) mfix -> wf (tFix mfix idx)
  | wf_tCoFix mfix idx : wf (tCoFix mfix idx).

  Fixpoint consts (t : term) : list kername :=
    match t with
    | tConst kn => [kn]
    | tLambda _ b => consts b
    | tLetIn _ b b' => consts b ++ consts b'
    | tApp f a => consts f ++ consts a
    | tConstruct _ _ args => flat_map consts args
    | tCase _ d brs => consts d ++ flat_map (fun br => consts br.2) brs
    | tFix mfix _ => flat_map (fun d => consts d.(dbody)) mfix
    | _ => []
    end.

  Definition compile_mfix (mfix : list (ident * term)) : list (varN * varN * exp) :=
    map (fun '(n, b) => let '(arg, e) := force_lambda (compile Σ b) in (local_name n, arg, e)) mfix.

  Inductive vrel : value -> val -> Prop :=
  | vrel_Construct ind c mdecl idecl cdecl args ws :
      lookup_constructor Σ ind c = Some (mdecl, idecl, cdecl) ->
      Forall2 vrel args ws ->
      vrel (vConstruct ind c args) (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws)
  | vrel_Clos na b Γ env :
      wf b ->
      namespace.c _ env = ctor_env Σ ->
      (forall x v, EWcbvEvalNamed.lookup Γ x = Some v ->
         exists w, nsLookup val (namespace.v _ env) (Short (local_name x)) = Some w /\ vrel v w) ->
      (forall kn decl body v, In kn (consts b) -> declared_constant Σ kn decl -> cst_body decl = Some body ->
         EWcbvEvalNamed.eval Σ [] body v ->
         exists w, nsLookup val (namespace.v _ env) (Short (global_name Σ kn)) = Some w /\ vrel v w) ->
      vrel (vClos na b Γ) (Closure env (local_name na) (compile Σ b))
  | vrel_RecClos mfix idx Γ env :
      idx < #|mfix| ->
      NoDup (map fst mfix) ->
      Forall (fun d => isLambda d.2 /\ wf d.2) mfix ->
      namespace.c _ env = ctor_env Σ ->
      (forall x v, EWcbvEvalNamed.lookup Γ x = Some v ->
         exists w, nsLookup val (namespace.v _ env) (Short (local_name x)) = Some w /\ vrel v w) ->
      (forall kn decl body v, In kn (flat_map (fun d => consts d.2) mfix) -> declared_constant Σ kn decl -> cst_body decl = Some body ->
         EWcbvEvalNamed.eval Σ [] body v ->
         exists w, nsLookup val (namespace.v _ env) (Short (global_name Σ kn)) = Some w /\ vrel v w) ->
      vrel (vRecClos mfix idx Γ) (Recclosure env (compile_mfix mfix) (local_name (nth idx (map fst mfix) ""%bs))).

  Definition env_rel (Γ : environment) (ns : namespace modN varN val) :=
    forall x v, EWcbvEvalNamed.lookup Γ x = Some v ->
      exists w, nsLookup val ns (Short (local_name x)) = Some w /\ vrel v w.

  Definition globals_rel (ks : list kername) (ns : namespace modN varN val) :=
    forall kn decl body v, In kn ks -> declared_constant Σ kn decl -> cst_body decl = Some body ->
      EWcbvEvalNamed.eval Σ [] body v ->
      exists w, nsLookup val ns (Short (global_name Σ kn)) = Some w /\ vrel v w.

  Lemma globals_rel_incl ks ks' ns : incl ks' ks -> globals_rel ks ns -> globals_rel ks' ns.
  Proof. intros Hi H kn decl body v Hin. apply H. now apply Hi. Qed.

  Lemma globals_rel_ext ks ns ns' :
    (forall kn, nsLookup val ns' (Short (global_name Σ kn)) = nsLookup val ns (Short (global_name Σ kn))) ->
    globals_rel ks ns -> globals_rel ks ns'.
  Proof. intros Heq H kn decl body v Hin Hd Hb Hev. rewrite Heq. eauto. Qed.

  Lemma env_rel_add Γ ns x v w :
    env_rel Γ ns -> vrel v w -> env_rel (add x v Γ) (nsBind (local_name x) w ns).
  Proof.
    intros H Hv y v' Hl. rewrite nsLookup_nsBind. rewrite lookup_add in Hl.
    destruct (eqb_spec y x) as [->|Hne].
    - injection Hl as <-. rewrite Strings.String.eqb_refl. eauto.
    - destruct (Strings.String.eqb_spec (local_name x) (local_name y)) as [Heq|].
      + apply local_name_inj in Heq. congruence.
      + eauto.
  Qed.

  Lemma globals_rel_bind ks ns x w :
    globals_rel ks ns -> globals_rel ks (nsBind (local_name x) w ns).
  Proof.
    apply globals_rel_ext. intros kn. rewrite nsLookup_nsBind.
    destruct (Strings.String.eqb_spec (local_name x) (global_name Σ kn)) as [Heq|]; [|reflexivity].
    now apply local_global_name in Heq.
  Qed.

End Correctness.

Lemma map_fst_map2_pair {A B} (l1 : list A) (l2 : list B) :
  #|l1| = #|l2| -> map fst (map2 pair l1 l2) = l1.
Proof.
  induction l1 in l2 |- *; destruct l2; cbn; try lia; auto.
  intros H. f_equal. apply IHl1. lia.
Qed.

Lemma In_map2_pair_nth {A B} (l1 : list A) (l2 : list B) i x y :
  nth_error l1 i = Some x -> nth_error l2 i = Some y -> In (x, y) (map2 pair l1 l2).
Proof.
  induction l1 in l2, i |- *; destruct l2, i; cbn; try discriminate.
  - intros [= ->] [= ->]. now left.
  - intros H1 H2. right. eauto.
Qed.

Lemma NoDup_map_inj {A B} (f : A -> B) l :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj. induction 1; cbn; constructor; auto.
  intros (x' & Heq & Hin)%in_map_iff. apply Hinj in Heq. congruence.
Qed.

Lemma nsLookup_nsAppend_alist l (ns : namespace modN varN val) k :
  nsLookup val (nsAppend (alist_to_ns l) ns) (Short k) =
    match ALOOKUP val l k with Some x => Some x | None => nsLookup val ns (Short k) end.
Proof. destruct ns. cbn. apply ALOOKUP_app. Qed.

Lemma nsLookup_local_ext l (ns : namespace modN varN val) Σ kn :
  (forall k, In k (map fst l) -> exists x, k = local_name x) ->
  nsLookup val (nsAppend (alist_to_ns l) ns) (Short (global_name Σ kn)) = nsLookup val ns (Short (global_name Σ kn)).
Proof.
  intros Hl. rewrite nsLookup_nsAppend_alist.
  rewrite ALOOKUP_notin; [reflexivity|].
  intros Hin. destruct (Hl _ Hin) as [x Hx]. symmetry in Hx. now apply local_global_name in Hx.
Qed.

Lemma fold_rec_lookup_In full cl_env (ns : namespace modN varN val) name (l : list (varN * varN * exp)) :
  In name (map (fun '(x, _, _) => x) l) ->
  nsLookup val (fold_right (fun '(f, _, _) env' => nsBind f (Recclosure cl_env full f) env') ns l) (Short name) =
    Some (Recclosure cl_env full name).
Proof.
  induction l as [|[[f x] e] l IH]; cbn [fold_right map In]; [tauto|].
  intros Hin. rewrite nsLookup_nsBind.
  destruct (Strings.String.eqb_spec f name) as [->|Hne]; [reflexivity|].
  apply IH. destruct Hin; [congruence|assumption].
Qed.

Lemma fold_rec_lookup_notIn full cl_env (ns : namespace modN varN val) name (l : list (varN * varN * exp)) :
  ~ In name (map (fun '(x, _, _) => x) l) ->
  nsLookup val (fold_right (fun '(f, _, _) env' => nsBind f (Recclosure cl_env full f) env') ns l) (Short name) =
    nsLookup val ns (Short name).
Proof.
  induction l as [|[[f x] e] l IH]; cbn [fold_right map In]; [reflexivity|].
  intros Hin. rewrite nsLookup_nsBind.
  destruct (Strings.String.eqb_spec f name) as [->|Hne]; [tauto|].
  apply IH. tauto.
Qed.

Lemma build_rec_env_lookup_In funs cl_env (ns : namespace modN varN val) name :
  In name (map (fun '(x, _, _) => x) funs) ->
  nsLookup val (build_rec_env funs cl_env ns) (Short name) = Some (Recclosure cl_env funs name).
Proof. apply fold_rec_lookup_In. Qed.

Lemma build_rec_env_lookup_notIn funs cl_env (ns : namespace modN varN val) name :
  ~ In name (map (fun '(x, _, _) => x) funs) ->
  nsLookup val (build_rec_env funs cl_env ns) (Short name) = nsLookup val ns (Short name).
Proof. apply fold_rec_lookup_notIn. Qed.

Lemma find_recfun_nth (funs : list (varN * varN * exp)) i f x e :
  NoDup (map (fun '(f, _, _) => f) funs) ->
  nth_error funs i = Some (f, x, e) ->
  find_recfun varN exp f funs = Some (x, e).
Proof.
  induction funs as [|[[f' x'] e'] funs IH] in i |- *; destruct i; cbn; try discriminate.
  - intros _ [= -> -> ->]. now rewrite Strings.String.eqb_refl.
  - intros Hnd Hn. inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct (Strings.String.eqb_spec f' f) as [->|]; [|eauto].
    exfalso. apply Hni. apply nth_error_In in Hn.
    now apply (in_map (fun '(f, _, _) => f)) in Hn.
Qed.

Lemma pmatch_list_pvars cenv names vs env :
  #|names| = #|vs| ->
  pmatch_list_helper pmatch cenv (map Pvar names) vs env =
    Match env_l (List.app (List.rev (map2 pair names vs)) env).
Proof.
  induction names in vs, env |- *; destruct vs; cbn; intros; try lia.
  - reflexivity.
  - rewrite IHnames by lia. now rewrite <- List.app_assoc.
Qed.

Lemma pat_bindings_pvars names acc :
  pat_bindings_list_helper pat_bindings (map Pvar names) acc = List.app (List.rev names) acc.
Proof.
  induction names in acc |- *; cbn; [reflexivity|].
  rewrite IHnames. now rewrite <- List.app_assoc.
Qed.

Lemma pat_bindings_panys n acc :
  pat_bindings_list_helper pat_bindings (repeat Pany n) acc = acc.
Proof. induction n; cbn; auto. Qed.

Lemma case_pattern_shape name n binders :
  exists ps, case_pattern name n binders = Pcon (Some (Short name)) ps /\ #|ps| = n /\
    ALL_DISTINCT_rel conN (pat_bindings (Pcon (Some (Short name)) ps) []).
Proof.
  unfold case_pattern.
  destruct (Nat.eqb_spec #|map (fun x => local_name (string_of_name x)) binders| n) as [Hn|];
    [destruct ALL_DISTINCT eqn:Hd|]; cbn.
  - eexists; split; [reflexivity|]. split.
    + now rewrite List.length_rev, List.length_map.
    + rewrite <- List.map_rev, pat_bindings_pvars, List.rev_involutive, List.app_nil_r.
      apply eq_distinct_list_rel. now apply eq_distinct_list.
  - eexists; split; [reflexivity|]. split; [apply repeat_length|].
    rewrite pat_bindings_panys. constructor.
  - eexists; split; [reflexivity|]. split; [apply repeat_length|].
    rewrite pat_bindings_panys. constructor.
Qed.

Lemma case_pattern_pvars name nms :
  NoDup nms ->
  case_pattern name #|nms| (map nNamed nms) = Pcon (Some (Short name)) (List.rev (map Pvar (map local_name nms))).
Proof.
  intros Hnd. unfold case_pattern.
  rewrite map_map. cbn.
  rewrite List.length_map, Nat.eqb_refl.
  replace (ALL_DISTINCT _ _ _) with true; [reflexivity|].
  symmetry. apply eq_distinct_list. apply NoDup_map_inj; [apply local_name_inj|exact Hnd].
Qed.

Lemma pmatch_pcon_other cenv n_i k ps n_c ws env :
  nsLookup (nat * stamp) cenv (Short n_i) = Some (k, TypeStamp n_i 0) ->
  #|ps| = k -> n_i <> n_c ->
  pmatch cenv (Pcon (Some (Short n_i)) ps) (Conv (Some (TypeStamp n_c 0)) ws) env = No_match env_l.
Proof.
  intros Hl Hk Hne. cbn [pmatch]. rewrite Hl. cbn.
  rewrite Hk, Nat.eqb_refl. cbn.
  destruct (Strings.String.eqb_spec n_i n_c); [congruence|reflexivity].
Qed.

Lemma pmatch_pcon_same cenv n k ps ws env :
  nsLookup (nat * stamp) cenv (Short n) = Some (k, TypeStamp n 0) ->
  #|ps| = k -> #|ws| = k ->
  pmatch cenv (Pcon (Some (Short n)) ps) (Conv (Some (TypeStamp n 0)) ws) env =
    pmatch_list_helper pmatch cenv ps ws env.
Proof.
  intros Hl Hk Hw. cbn [pmatch]. rewrite Hl. cbn.
  rewrite Hk, Nat.eqb_refl, Strings.String.eqb_refl, Hw, Nat.eqb_refl. reflexivity.
Qed.

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
    cbn in Hnth. injection Hnth as -> ->.
    eapply evaluate_match_M; eauto.
  - destruct pes as [|[p0 e0] pes']; [discriminate|].
    destruct (Hprev 0 p0 e0 ltac:(lia) eq_refl) as [Hdist0 Hnm0].
    eapply evaluate_match_NM; eauto.
    eapply IHc; eauto.
    intros i0 p0' e0' Hi0 Hnth0'. apply (Hprev (S i0) p0' e0'); [lia | exact Hnth0'].
Qed.

Lemma can_pmatch_all_forall cenv0 pats v0 :
  (forall p, In p pats -> is_Match_type_error (pmatch cenv0 p v0 []) = false) ->
  can_pmatch_all cenv0 pats v0 = true.
Proof.
  induction pats; cbn; intros H; auto.
  rewrite H; [|now left]. apply IHpats. intros p Hin. apply H. now right.
Qed.

Lemma In_map2_idx {A B C} (f : A -> B -> C) l1 l2 z :
  In z (map2 f l1 l2) ->
  exists i x y, nth_error l1 i = Some x /\ nth_error l2 i = Some y /\ z = f x y.
Proof.
  revert l2. induction l1; intros [|b l2]; cbn; try (intros []; fail).
  intros [Heq | Hin].
  - subst. exists 0, a, b. auto.
  - destruct (IHl1 l2 Hin) as (i & x & y & H1 & H2 & H3).
    exists (S i), x, y. auto.
Qed.

Lemma nth_error_map2 {A B C} (f : A -> B -> C) n l1 l2 x y :
  nth_error l1 n = Some x -> nth_error l2 n = Some y ->
  nth_error (map2 f l1 l2) n = Some (f x y).
Proof.
  revert n l2. induction l1; destruct n, l2; cbn; try discriminate; auto.
  intros [= ->] [= ->]. reflexivity.
Qed.

Lemma nth_error_map2_inv {A B C} (f : A -> B -> C) n l1 l2 z :
  nth_error (map2 f l1 l2) n = Some z ->
  exists x y, nth_error l1 n = Some x /\ nth_error l2 n = Some y /\ z = f x y.
Proof.
  revert n l2. induction l1; destruct n, l2; cbn; try discriminate.
  - intros [= <-]. eauto.
  - exact (IHl1 n l2).
Qed.

Lemma map2_InP_gen {A1 A2 B} (l1 : list A1) (l2 : list A2)
  (f : forall (a : A1) (b : A2), In a l1 -> In b l2 -> B) (g : A1 -> A2 -> B) :
  (forall x y (H1 : In x l1) (H2 : In y l2), f x y H1 H2 = g x y) ->
  map2_InP l1 l2 f = map2 g l1 l2.
Proof.
  revert l2 f. induction l1 as [|x xs IH]; intros l2 f Hext.
  - simp map2_InP. reflexivity.
  - destruct l2 as [|y ys].
    + simp map2_InP. reflexivity.
    + simp map2_InP. cbn. f_equal.
      * apply Hext.
      * apply IH. intros a b Ha Hb. apply Hext.
Qed.

Lemma evaluate_list_app env es1 es2 vs1 vs2 :
  evaluate_list env es1 (Rval_l vs1) ->
  evaluate_list env es2 (Rval_l vs2) ->
  evaluate_list env (List.app es1 es2) (Rval_l (List.app vs1 vs2)).
Proof.
  induction es1 in vs1 |- *; intros H1 H2.
  - inversion H1; subst. exact H2.
  - inversion H1; subst. cbn. econstructor; eauto.
Qed.

Lemma lookup_constructor_decompose Σ0 ind c mdecl idecl cdecl :
  lookup_constructor Σ0 ind c = Some (mdecl, idecl, cdecl) ->
  lookup_inductive Σ0 ind = Some (mdecl, idecl) /\
  nth_error (ind_ctors idecl) c = Some cdecl.
Proof.
  unfold lookup_constructor.
  destruct (lookup_inductive Σ0 ind) as [[m i]|] eqn:Hind; cbn; [|discriminate].
  destruct (nth_error (ind_ctors i) c) as [cd|] eqn:Hc; cbn; [|discriminate].
  intros H; injection H; intros; subst; auto.
Qed.

Lemma force_lambda_compile_Lambda Σ0 na fn :
  force_lambda (compile Σ0 (tLambda na fn)) = (local_name (string_of_name na), compile Σ0 fn).
Proof. simp compile. reflexivity. Qed.

Lemma compile_mfix_names Σ0 mfix :
  map (fun '(f, _, _) => f) (compile_mfix Σ0 mfix) = map local_name (map fst mfix).
Proof.
  induction mfix as [|[n b] mfix IH]; cbn; [reflexivity|].
  destruct force_lambda. cbn. now f_equal.
Qed.

Lemma nth_error_compile_mfix Σ0 mfix idx na' na fn :
  nth_error mfix idx = Some (na', tLambda (nNamed na) fn) ->
  nth_error (compile_mfix Σ0 mfix) idx = Some (local_name na', local_name na, compile Σ0 fn).
Proof.
  intros H. unfold compile_mfix. rewrite nth_error_map, H. cbn.
  now rewrite force_lambda_compile_Lambda.
Qed.

Lemma compile_mfix_nth_name Σ0 (l : list (ident * term)) i d d' :
  i < #|l| -> fst (fst (nth i (compile_mfix Σ0 l) d)) = local_name (nth i (map fst l) d').
Proof.
  unfold compile_mfix. induction l as [|[n0 b0] l IH] in i |- *; intros Hi; destruct i; cbn in *; try lia.
  - destruct force_lambda; reflexivity.
  - apply IH. lia.
Qed.

Lemma Forall2_nth_error_l {A B} (R : A -> B -> Prop) l l' i x :
  Forall2 R l l' -> nth_error l i = Some x -> exists y, nth_error l' i = Some y /\ R x y.
Proof.
  intros H. induction H in i |- *; destruct i; cbn; try discriminate.
  - intros [= ->]. eauto.
  - apply IHForall2.
Qed.

Section Simulation.
  Context (Σ : global_declarations).

  Lemma env_rel_add_multiple Γ ns ks vs ws :
    NoDup ks -> #|ks| = #|vs| -> Forall2 (vrel Σ) vs ws -> env_rel Σ Γ ns ->
    env_rel Σ (add_multiple ks vs Γ)
      (nsAppend (alist_to_ns (List.rev (map2 pair (map local_name ks) ws))) ns).
  Proof.
    intros Hnd Hlen Hf H y v Hl.
    assert (Hlw : #|vs| = #|ws|) by (eapply Forall2_length; eauto).
    assert (Hkeys : map fst (List.rev (map2 pair (map local_name ks) ws)) = List.rev (map local_name ks)).
    { rewrite List.map_rev, map_fst_map2_pair; [reflexivity|]. rewrite List.length_map. lia. }
    rewrite nsLookup_nsAppend_alist.
    apply lookup_add_multiple_inv in Hl as [(i & H1 & H2)|[Hn H']]; [| |exact Hlen].
    - destruct (Forall2_nth_error_l _ _ _ _ _ Hf H2) as (w & Hw & Hr).
      exists w. split; [|exact Hr].
      rewrite (ALOOKUP_NoDup _ _ w); [reflexivity| |].
      + rewrite Hkeys. apply NoDup_rev. apply NoDup_map_inj; [apply local_name_inj|exact Hnd].
      + rewrite <- List.in_rev. eapply In_map2_pair_nth; [|exact Hw].
        now rewrite nth_error_map, H1.
    - rewrite ALOOKUP_notin; [now apply H|].
      rewrite Hkeys, <- List.in_rev. intros (y' & Heq & Hin)%in_map_iff.
      apply local_name_inj in Heq. subst. tauto.
  Qed.

  Lemma env_rel_fix Γ' env mfix :
    NoDup (map fst mfix) ->
    Forall (fun d => isLambda d.2 /\ wf Σ d.2) mfix ->
    namespace.c _ env = ctor_env Σ ->
    env_rel Σ Γ' (namespace.v _ env) ->
    globals_rel Σ (flat_map (fun d => consts d.2) mfix) (namespace.v _ env) ->
    env_rel Σ (add_multiple (List.rev (map fst mfix)) (fix_env mfix Γ') Γ')
      (build_rec_env (compile_mfix Σ mfix) env (namespace.v _ env)).
  Proof.
    intros Hnd Hbodies Hc Henv Hglob y v Hl.
    apply lookup_fix_env in Hl as [(j & Hj & ->)|[Hn Hl]].
    - eexists. rewrite build_rec_env_lookup_In.
      + split; [reflexivity|].
        rewrite <- (nth_error_nth _ _ ""%bs Hj).
        apply vrel_RecClos; auto.
        apply nth_error_Some_length in Hj. now rewrite List.length_map in Hj.
      + rewrite compile_mfix_names. apply in_map. now eapply nth_error_In.
    - rewrite build_rec_env_lookup_notIn; [now apply Henv|].
      rewrite compile_mfix_names. intros (y' & Heq & Hin)%in_map_iff.
      apply local_name_inj in Heq. subst. tauto.
  Qed.

  Lemma globals_rel_rec ks env funs :
    (forall k, In k (map (fun '(x, _, _) => x) funs) -> exists x, k = local_name x) ->
    globals_rel Σ ks (namespace.v _ env) ->
    globals_rel Σ ks (build_rec_env funs env (namespace.v _ env)).
  Proof.
    intros Hl. apply globals_rel_ext. intros kn.
    apply build_rec_env_lookup_notIn. intros Hin.
    destruct (Hl _ Hin) as [x Hx]. symmetry in Hx. now apply local_global_name in Hx.
  Qed.

  Lemma case_match_correct env ind mdecl idecl c cdecl ws brs binders body nms bv :
    namespace.c _ env = ctor_env Σ ->
    lookup_inductive Σ ind = Some (mdecl, idecl) ->
    nth_error (ind_ctors idecl) c = Some cdecl ->
    nth_error brs c = Some (binders, body) ->
    #|ws| = cstr_nargs cdecl ->
    #|nms| = cstr_nargs cdecl ->
    binders = map nNamed nms ->
    NoDup nms ->
    evaluate {| v := nsAppend (alist_to_ns (List.rev (map2 pair (map local_name (List.rev nms)) ws))) (namespace.v _ env);
                c := namespace.c _ env |} (compile Σ body) bv ->
    let pes := map2 (fun '(name, nargs) '(binders, body) => (case_pattern name nargs binders, compile Σ body))
                 (mapi (fun c cdecl => (ctor_name c cdecl, cstr_nargs cdecl)) (ind_ctors idecl)) brs in
    evaluate_match env (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws) pes bind_exn_v bv /\
    can_pmatch_all (namespace.c _ env) (map fst pes) (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws) = true.
  Proof.
    intros Hc Hind Hcd Hbr Hws Hnms -> Hnd Hev pes.
    set (pc := Pcon (Some (Short (ctor_name c cdecl))) (List.rev (map Pvar (map local_name nms)))).
    assert (Hpc : case_pattern (ctor_name c cdecl) (cstr_nargs cdecl) (map nNamed nms) = pc).
    { rewrite <- Hnms. now apply case_pattern_pvars. }
    assert (Hnth : nth_error pes c = Some (pc, compile Σ body)).
    { unfold pes. erewrite nth_error_map2; [|now rewrite nth_error_mapi, Hcd|exact Hbr].
      cbv beta iota. now rewrite Hpc. }
    assert (Hlk : forall i cdecl_i, nth_error (ind_ctors idecl) i = Some cdecl_i ->
      nsLookup (nat * stamp) (namespace.c _ env) (Short (ctor_name i cdecl_i)) =
        Some (cstr_nargs cdecl_i, TypeStamp (ctor_name i cdecl_i) 0)).
    { intros i cdecl_i Hi. rewrite Hc. eapply ctor_env_lookup; eauto. }
    assert (Hmatch : pmatch (namespace.c _ env) pc (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws) [] =
      Match env_l (List.rev (map2 pair (map local_name (List.rev nms)) ws))).
    { unfold pc. rewrite (pmatch_pcon_same _ _ (cstr_nargs cdecl) _ _ _ (Hlk _ _ Hcd)).
      - rewrite <- List.map_rev, pmatch_list_pvars.
        + now rewrite List.app_nil_r, List.map_rev.
        + now rewrite List.length_rev, List.length_map.
      - now rewrite List.length_rev, !List.length_map.
      - exact Hws. }
    assert (Hother : forall i p e, i <> c -> nth_error pes i = Some (p, e) ->
      ALL_DISTINCT_rel conN (pat_bindings p []) /\
      pmatch (namespace.c _ env) p (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws) [] = No_match env_l).
    { intros i p e Hne Hi. unfold pes in Hi.
      apply nth_error_map2_inv in Hi as ([name_i nargs_i] & [binders_i body_i] & Hx & _ & Heq).
      rewrite nth_error_mapi in Hx.
      destruct (nth_error (ind_ctors idecl) i) as [cdecl_i|] eqn:Hci; [|discriminate].
      cbn [option_map] in Hx. injection Hx as <- <-. cbv beta iota in Heq. injection Heq as -> ->.
      destruct (case_pattern_shape (ctor_name i cdecl_i) (cstr_nargs cdecl_i) binders_i) as (ps & -> & Hlen & Hd).
      split; [exact Hd|].
      eapply pmatch_pcon_other; [exact (Hlk _ _ Hci)|exact Hlen|].
      intros Heq. apply ctor_name_inj in Heq as [? _]. congruence. }
    split.
    - eapply (evaluate_match_nth _ _ _ _ _ c); [exact Hnth| | |exact Hmatch|exact Hev].
      + intros i pi ei Hi Hni. apply (Hother i pi ei); [lia|exact Hni].
      + destruct (case_pattern_shape (ctor_name c cdecl) (cstr_nargs cdecl) (map nNamed nms)) as (ps & Heq & _ & Hd).
        rewrite Hpc in Heq. now rewrite Heq.
    - apply can_pmatch_all_forall. intros p (pe & <- & Hin)%in_map_iff.
      apply In_nth_error in Hin as [i Hi].
      destruct pe as [p e]. cbn [fst].
      destruct (Nat.eq_dec i c) as [->|Hne].
      + rewrite Hnth in Hi. injection Hi as <- <-. now rewrite Hmatch.
      + destruct (Hother i p e Hne Hi) as [_ ->]. reflexivity.
  Qed.

  Lemma compile_fix_bodies (mfix : list (def term)) nms :
    Forall2 (fun d n => nNamed n = dname d) mfix nms ->
    map (fun d => let '(arg, expr) := force_lambda (compile Σ (dbody d)) in
      (local_name (string_of_name (dname d)), arg, expr)) mfix =
    compile_mfix Σ (map2 (fun n d => (n, dbody d)) nms mfix).
  Proof.
    induction 1; cbn; [reflexivity|].
    rewrite <- H. cbn. destruct force_lambda. f_equal. exact IHForall2.
  Qed.

  Definition sim_goal Γ t v : Prop :=
    forall env, wf Σ t -> namespace.c _ env = ctor_env Σ ->
      env_rel Σ Γ (namespace.v _ env) -> globals_rel Σ (consts t) (namespace.v _ env) ->
      exists w, evaluate env (compile Σ t) (Rval w) /\ vrel Σ v w.

  Lemma eval_args_correct Γ env args args' (a : All2_Set (eval Σ Γ) args args') :
    All2_over a (fun t v _ => sim_goal Γ t v) ->
    Forall (wf Σ) args ->
    namespace.c _ env = ctor_env Σ ->
    env_rel Σ Γ (namespace.v _ env) ->
    globals_rel Σ (flat_map consts args) (namespace.v _ env) ->
    exists ws, evaluate_list env (List.rev (map (compile Σ) args)) (Rval_l (List.rev ws)) /\
      Forall2 (vrel Σ) args' ws.
  Proof.
    intros IHa Hwf Hc Henv. revert IHa Hwf.
    induction a as [|x y l l' r a IH]; intros IHa Hwf Hglob; cbn in *.
    - exists []. split; [constructor|constructor].
    - destruct IHa as [IHx IHl]. inversion Hwf; subst.
      destruct (IHx env ltac:(assumption) Hc Henv) as (w & Hw & Hr).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appl, incl_refl. }
      destruct (IH IHl ltac:(assumption)) as (ws & Hws & Hrs).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appr, incl_refl. }
      exists (w :: ws). split; [|constructor; auto].
      cbn. eapply evaluate_list_app; [exact Hws|].
      econstructor; [exact Hw|constructor].
  Qed.

  Lemma compile_correct Γ s v :
    eval Σ Γ s v -> sim_goal Γ s v.
  Proof.
    intros ev. unfold sim_goal.
    induction ev using eval_ind; intros env Hwf Hc Henv Hglob.
    -
      destruct (Henv _ _ e) as (w & Hl & Hr).
      exists w. simp compile. split; [now constructor|exact Hr].
    -
      inversion Hwf; subst. cbn [consts] in Hglob.
      destruct (IHev1 env ltac:(assumption) Hc Henv) as (w1 & Hw1 & Hr1).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appl, incl_refl. }
      destruct (IHev2 env ltac:(assumption) Hc Henv) as (w2 & Hw2 & Hr2).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appr, incl_refl. }
      inversion Hr1 as [| ? ? ? env' Hwfb Hc' Henv' Hglob' | ]; subst.
      destruct (IHev3 {| v := nsBind (local_name na) w2 (namespace.v _ env'); c := namespace.c _ env' |})
        as (w3 & Hw3 & Hr3); cbn [namespace.v namespace.c]; auto.
      + now apply env_rel_add.
      + apply globals_rel_bind. exact Hglob'.
      + exists w3. split; [|exact Hr3]. simp compile.
        eapply evaluate_App with (vs := [w2; _]).
        * cbn. econstructor; [exact Hw2|]. econstructor; [exact Hw1|]. constructor.
        * reflexivity.
        * exact Hw3.
        * constructor.
    -
      inversion Hwf; subst.
      eexists. simp compile. split; [constructor|].
      apply vrel_Clos; auto.
    -
      inversion Hwf; subst. cbn [consts] in Hglob.
      destruct (IHev1 env ltac:(assumption) Hc Henv) as (w1 & Hw1 & Hr1).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appl, incl_refl. }
      destruct (IHev2 {| v := nsBind (local_name na) w1 (namespace.v _ env); c := namespace.c _ env |})
        as (w2 & Hw2 & Hr2); cbn [namespace.v namespace.c]; auto.
      + now apply env_rel_add.
      + apply globals_rel_bind. eapply globals_rel_incl; [|exact Hglob]. apply incl_appr, incl_refl.
      + exists w2. split; [|exact Hr2]. simp compile.
        eapply evaluate_Let; [exact Hw1|]. exact Hw2.
    -
      inversion Hwf as [| | | | | | | | |? ? ? Hwfd Hwfbrs| | |]; subst. cbn [consts] in Hglob.
      destruct (IHev1 env Hwfd Hc Henv) as (w1 & Hw1 & Hr1).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appl, incl_refl. }
      unfold constructor_isprop_pars_decl in e0.
      destruct (lookup_constructor Σ ind c) as [[[mdecl idecl] cdecl']|] eqn:Hlc; cbn in e0; [|discriminate].
      injection e0 as _ _ ->.
      destruct (lookup_constructor_decompose _ _ _ _ _ _ Hlc) as [Hind Hcd].
      inversion Hr1 as [? ? mdecl' idecl' cdecl'' ? ws Hlc' Hargs| |]; subst.
      rewrite Hlc in Hlc'. injection Hlc' as <- <- <-.
      destruct br as [binders body]. cbn [fst snd] in *.
      assert (Hbinders : binders = map nNamed nms).
      { clear -f4. induction f4; cbn; congruence. }
      assert (Hnms : #|nms| = #|args|).
      { rewrite e3, Hbinders. now rewrite List.length_map. }
      assert (Hws : #|ws| = #|args|) by (symmetry; eapply Forall2_length; eauto).
      destruct (IHev2 {| v := nsAppend (alist_to_ns (List.rev (map2 pair (map local_name (List.rev nms)) ws))) (namespace.v _ env);
                         c := namespace.c _ env |}) as (w2 & Hw2 & Hr2); cbn [namespace.v namespace.c]; auto.
      + rewrite Forall_forall in Hwfbrs. apply (Hwfbrs (binders, body)). now eapply nth_error_In.
      + apply env_rel_add_multiple; auto.
        * now apply NoDup_rev.
        * rewrite List.length_rev. lia.
      + apply globals_rel_ext with (ns := namespace.v _ env).
        { intros kn. apply nsLookup_local_ext.
          intros k Hk. rewrite List.map_rev, map_fst_map2_pair, <- List.in_rev in Hk.
          - apply in_map_iff in Hk as (x & <- & _). eauto.
          - rewrite List.length_map, List.length_rev. lia. }
        eapply globals_rel_incl; [|exact Hglob]. apply incl_appr.
        intros kn Hkn. apply in_flat_map. exists (binders, body). split; [now eapply nth_error_In|exact Hkn].
      + exists w2. split; [|exact Hr2]. simp compile. cbn [fst].
        unfold lookup_constructor_names. rewrite Hind.
        rewrite (map2_InP_gen _ _ _ (fun '(name, nargs) '(binders, body) => (case_pattern name nargs binders, compile Σ body)));
          [|intros [] [] _ _; reflexivity].
        destruct (case_match_correct env ind mdecl idecl c cdecl ws brs binders body nms (Rval w2))
          as [Hm Hcan]; auto; try lia.
        eapply evaluate_Mat; [exact Hw1|exact Hm|exact Hcan].
    -
      inversion Hwf; subst. cbn [consts] in Hglob.
      destruct (IHev1 env ltac:(assumption) Hc Henv) as (w1 & Hw1 & Hr1).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appl, incl_refl. }
      destruct (IHev3 env ltac:(assumption) Hc Henv) as (w2 & Hw2 & Hr2).
      { eapply globals_rel_incl; [|exact Hglob]. apply incl_appr, incl_refl. }
      inversion Hr1 as [| | ? ? ? env' Hidx Hnd Hbods Hc' Henv' Hglob']; subst.
      set (funs := compile_mfix Σ mfix).
      assert (Hin : In (na', tLambda (nNamed na) fn) mfix) by (now eapply nth_error_In).
      assert (Hwffn : wf Σ fn).
      { rewrite Forall_forall in Hbods. destruct (Hbods _ Hin) as [_ Hw]. now inversion Hw. }
      destruct (IHev2 {| v := nsBind (local_name na) w2 (build_rec_env funs env' (namespace.v _ env'));
                         c := namespace.c _ env' |}) as (w3 & Hw3 & Hr3); cbn [namespace.v namespace.c]; auto.
      + apply env_rel_add; [|exact Hr2]. now apply env_rel_fix.
      + apply globals_rel_bind. apply globals_rel_rec.
        { intros k Hk. unfold funs in Hk. rewrite compile_mfix_names in Hk.
          apply in_map_iff in Hk as (x & <- & _). eauto. }
        eapply globals_rel_incl; [|exact Hglob'].
        intros kn Hkn. apply in_flat_map. exists (na', tLambda (nNamed na) fn). split; [exact Hin|exact Hkn].
      + exists w3. split; [|exact Hr3]. simp compile.
        eapply evaluate_App with (vs := [w2; Recclosure env' funs (local_name (nth idx (map fst mfix) ""%bs))]).
        * cbn. econstructor; [exact Hw2|]. econstructor; [exact Hw1|]. constructor.
        * cbn [List.rev List.app do_opapp].
          replace (ALL_DISTINCT _ _ _) with true.
          2:{ symmetry. apply eq_distinct_list. unfold funs. rewrite compile_mfix_names.
              apply NoDup_map_inj; [apply local_name_inj|exact Hnd]. }
          erewrite nth_error_nth by (now rewrite nth_error_map, e0).
          rewrite (find_recfun_nth _ idx _ (local_name na) (compile Σ fn)); [reflexivity| |].
          -- unfold funs. rewrite compile_mfix_names.
             apply NoDup_map_inj; [apply local_name_inj|exact Hnd].
          -- now apply nth_error_compile_mfix.
        * exact Hw3.
        * constructor.
    -
      inversion Hwf as [| | | | | | | | | | |? ? Hwfm|]; subst.
      set (mfix' := map2 (fun n d => (n, dbody d)) nms mfix).
      assert (Hlnms : #|nms| = #|mfix|) by (symmetry; eapply Forall2_length; eauto).
      assert (Hnames : map fst mfix' = nms).
      { unfold mfix'. clear -Hlnms. induction nms in mfix, Hlnms |- *; destruct mfix; cbn in *; try lia; auto.
        f_equal. apply IHnms. lia. }
      assert (Hbodies' : map snd mfix' = map dbody mfix).
      { unfold mfix'. clear -Hlnms. induction nms in mfix, Hlnms |- *; destruct mfix; cbn in *; try lia; auto.
        f_equal. apply IHnms. lia. }
      assert (Hconsts : flat_map (fun d => consts d.2) mfix' = flat_map (fun d => consts (dbody d)) mfix).
      { unfold mfix'. clear -Hlnms. induction nms in mfix, Hlnms |- *; destruct mfix; cbn in *; try lia; auto.
        f_equal. apply IHnms. lia. }
      set (funs := compile_mfix Σ mfix').
      set (name := local_name (nth idx (map fst mfix') ""%bs)).
      exists (Recclosure env funs name). split.
      + simp compile. rewrite map_InP_spec. rewrite (compile_fix_bodies mfix nms f6). fold mfix' funs.
        cbv zeta. match goal with |- context [nth idx funs ?d] => replace (fst (fst (nth idx funs d))) with name end.
        2:{ unfold name, funs. symmetry. apply compile_mfix_nth_name.
            rewrite <- (List.length_map fst), Hnames. lia. }
        apply evaluate_Letrec.
        * apply eq_distinct_list_rel. unfold funs. rewrite compile_mfix_names, Hnames.
          apply NoDup_map_inj; [apply local_name_inj|exact n].
        * constructor. apply build_rec_env_lookup_In.
          unfold funs, name. rewrite compile_mfix_names. apply in_map.
          apply nth_In. rewrite Hnames. lia.
      + apply vrel_RecClos; auto.
        * rewrite <- (List.length_map fst), Hnames. lia.
        * now rewrite Hnames.
        * rewrite Forall_forall in Hwfm |- *. intros [n0 b] Hin.
          assert (Hb : In b (map dbody mfix)) by (rewrite <- Hbodies'; now apply (in_map snd) in Hin).
          apply in_map_iff in Hb as (d & <- & Hd). cbn. split.
          -- exact (proj1 (forallb_forall _ _) Hbodies _ Hd).
          -- exact (Hwfm _ Hd).
        * now rewrite Hconsts.
    -
      destruct (Hglob c decl body res (or_introl eq_refl) isdecl e ev) as (w & Hl & Hr).
      exists w. simp compile. split; [now constructor|exact Hr].
    -
      inversion Hwf as [| | | | | | | |? ? ? Harity Hwfargs| | | |]; subst. cbn [consts] in Hglob.
      specialize (Harity _ _ _ e).
      destruct (lookup_constructor_decompose _ _ _ _ _ _ e) as [Hind Hcd].
      destruct (eval_args_correct Γ env args args' a IHa Hwfargs Hc Henv Hglob) as (ws & Hws & Hrs).
      exists (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) ws). split.
      + simp compile. unfold lookup_constructor_names. rewrite Hind, map_InP_spec.
        erewrite nth_error_nth by (now rewrite nth_error_mapi, Hcd).
        cbn [fst]. eapply evaluate_Con with (vs := List.rev ws).
        * unfold do_con_check. rewrite Hc, (ctor_env_lookup _ _ _ _ _ _ Hind Hcd).
          rewrite List.length_map, Harity. apply Nat.eqb_refl.
        * unfold build_conv. rewrite Hc, (ctor_env_lookup _ _ _ _ _ _ Hind Hcd).
          now rewrite List.rev_involutive.
        * exact Hws.
      + econstructor; eauto.
    -
      inversion Hwf as [| | | | | | | |? ? ? Harity Hwfargs| | | |]; subst.
      specialize (Harity _ _ _ e). cbn in Harity.
      destruct (lookup_constructor_decompose _ _ _ _ _ _ e) as [Hind Hcd].
      exists (Conv (Some (TypeStamp (ctor_name c cdecl) 0)) []). split.
      + simp compile. unfold lookup_constructor_names. rewrite Hind.
        erewrite nth_error_nth by (now rewrite nth_error_mapi, Hcd).
        cbn [fst]. simp map_InP. eapply evaluate_Con with (vs := []).
        * unfold do_con_check. rewrite Hc, (ctor_env_lookup _ _ _ _ _ _ Hind Hcd).
          cbn. now rewrite <- Harity.
        * unfold build_conv. rewrite Hc, (ctor_env_lookup _ _ _ _ _ _ Hind Hcd). reflexivity.
        * constructor.
      + econstructor; eauto.
    -  inversion Hwf.
    -  inversion Hwf.
    -  inversion Hwf.
  Qed.

End Simulation.

Inductive eval_decls : Sem_env val -> list (Kernames.ident * option exp) -> Sem_env val -> Prop :=
| eval_decls_nil env : eval_decls env [] env
| eval_decls_let env ds env' x e w :
    eval_decls env ds env' ->
    evaluate env' e (Rval w) ->
    eval_decls env ((x, Some e) :: ds)
      {| v := nsBind (String.to_string x) w (namespace.v _ env'); c := namespace.c _ env' |}.

Definition initial_env (Σ : global_declarations) : Sem_env val :=
  {| v := Bind modN varN val [] []; c := ctor_env Σ |}.

Lemma eval_decls_c env ds env' :
  eval_decls env ds env' -> namespace.c _ env' = namespace.c _ env.
Proof. induction 1; cbn; auto. Qed.

Lemma global_ident_at_inj i j kn kn' :
  String.to_string (global_ident_at i kn) = String.to_string (global_ident_at j kn') -> i = j.
Proof.
  unfold global_ident_at. intros H. apply to_string_injective in H.
  cbn in H. injection H as H.
  apply split_us in H as [H _]; try apply no_us_string_of_uint.
  now apply string_of_nat_inj.
Qed.

Lemma global_index_lt Σ kn d :
  lookup_env Σ kn = Some d -> global_index Σ kn < #|Σ|.
Proof.
  induction Σ as [|[kn' d'] Σ IH]; cbn; [discriminate|].
  destruct (eqb_spec kn kn'); [lia|]. intros Hl. specialize (IH Hl). lia.
Qed.

Lemma global_index_inj Σ kn1 kn2 d1 d2 :
  lookup_env Σ kn1 = Some d1 -> lookup_env Σ kn2 = Some d2 ->
  global_index Σ kn1 = global_index Σ kn2 -> kn1 = kn2.
Proof.
  induction Σ as [|[kn' d'] Σ IH]; cbn; [discriminate|].
  destruct (eqb_spec kn1 kn') as [->|]; destruct (eqb_spec kn2 kn') as [->|];
    intros H1 H2 Heq; try reflexivity.
  all: try (apply global_index_lt in H2; lia).
  all: try (apply global_index_lt in H1; lia).
  eauto.
Qed.

Definition env_sub (Σ' Σ : global_declarations) :=
  forall kn d, lookup_env Σ' kn = Some d -> lookup_env Σ kn = Some d /\ global_index Σ kn = global_index Σ' kn.

Lemma env_sub_refl Σ : env_sub Σ Σ.
Proof. now intros kn d H. Qed.

Lemma env_sub_trans Σ1 Σ2 Σ3 : env_sub Σ1 Σ2 -> env_sub Σ2 Σ3 -> env_sub Σ1 Σ3.
Proof.
  intros H12 H23 kn d H. destruct (H12 _ _ H) as [H2 E1].
  destruct (H23 _ _ H2) as [H3 E2]. split; [exact H3|congruence].
Qed.

Lemma env_sub_cons Σ kn d :
  fresh_global kn Σ -> env_sub Σ ((kn, d) :: Σ).
Proof.
  intros Hfr kn' d' Hl. cbn.
  destruct (eqb_spec kn' kn) as [->|]; auto.
  exfalso. eapply lookup_env_Some_fresh; eauto.
Qed.

Lemma env_sub_lookup_inductive Σ' Σ ind mdecl idecl :
  env_sub Σ' Σ -> lookup_inductive Σ' ind = Some (mdecl, idecl) -> lookup_inductive Σ ind = Some (mdecl, idecl).
Proof.
  intros Hs. unfold lookup_inductive, lookup_minductive.
  destruct (lookup_env Σ' (inductive_mind ind)) eqn:He; cbn; [|discriminate].
  now rewrite (proj1 (Hs _ _ He)).
Qed.

Lemma env_sub_lookup_constructor Σ' Σ ind c x :
  env_sub Σ' Σ -> lookup_constructor Σ' ind c = Some x -> lookup_constructor Σ ind c = Some x.
Proof.
  intros Hs H. unfold lookup_constructor in *.
  destruct (lookup_inductive Σ' ind) as [[mdecl idecl]|] eqn:Hl; [|discriminate].
  rewrite (env_sub_lookup_inductive _ _ _ _ _ Hs Hl). exact H.
Qed.

Lemma map2_ext_In {A B C} (f g : A -> B -> C) l1 l2 :
  (forall x y, In y l2 -> f x y = g x y) -> map2 f l1 l2 = map2 g l1 l2.
Proof.
  induction l1 in l2 |- *; destruct l2; cbn; auto.
  intros H. f_equal; auto.
Qed.

Section Program.
  Context {efl : EEnvFlags}.
  Context (Hax : has_axioms = false) (Hblocks : cstr_as_blocks = true)
    (Hprim : forall p : prim_val term, has_prim p = false) (Hlazy : has_tLazy_Force = false).

  Lemma compile_sub Σ' Σ k t :
    wellformed Σ' k t -> env_sub Σ' Σ -> compile Σ' t = compile Σ t.
  Proof.
    intros Hwf Hs. induction t in k, Hwf |- * using EInduction.term_forall_list_ind;
      cbn [wellformed] in Hwf; rtoProp; simp compile; try reflexivity.
    - now erewrite IHt.
    - now erewrite IHt1, IHt2.
    - now erewrite IHt1, IHt2.
    - destruct (lookup_constant Σ' s) as [d|] eqn:Hc; [|discriminate].
      unfold lookup_constant in Hc. destruct (lookup_env Σ' s) as [[]|] eqn:He; cbn in Hc; try discriminate.
      unfold global_name, global_ident. now rewrite (proj2 (Hs _ _ He)).
    - match goal with Hi : is_true (isSome (lookup_constructor _ _ _)) |- _ => rename Hi into Hsome end.
      match goal with Hb : is_true (if cstr_as_blocks then _ else _) |- _ => rename Hb into Hblk end.
      destruct (lookup_constructor Σ' i n) as [[[mdecl idecl] cdecl]|] eqn:Hlc; cbn in Hsome; [|discriminate].
      destruct (lookup_constructor_decompose _ _ _ _ _ _ Hlc) as [Hind _].
      unfold lookup_constructor_names. rewrite Hind, (env_sub_lookup_inductive _ _ _ _ _ Hs Hind).
      rewrite !map_InP_spec. rewrite Hblocks in Hblk. rtoProp.
      enough (Hmap : map (compile Σ') args = map (compile Σ) args) by now rewrite Hmap.
      solve_all.
    - match goal with Hb : is_true (wf_brs _ _ _) |- _ => rename Hb into Hbrs end.
      unfold wf_brs in Hbrs. destruct lookup_inductive as [[mdecl idecl]|] eqn:Hind; [|discriminate].
      unfold lookup_constructor_names. rewrite Hind, (env_sub_lookup_inductive _ _ _ _ _ Hs Hind).
      erewrite IHt; eauto. f_equal.
      rewrite (map2_InP_gen _ _ _ (fun '(name, nargs) '(binders, body) => (case_pattern name nargs binders, compile Σ' body)))
        by (intros [] [] _ _; reflexivity).
      rewrite (map2_InP_gen _ _ _ (fun '(name, nargs) '(binders, body) => (case_pattern name nargs binders, compile Σ body)))
        by (intros [] [] _ _; reflexivity).
      apply map2_ext_In. intros [name nargs] [binders body] Hin. cbn. f_equal.
      match goal with Hb : is_true (forallb _ l) |- _ => rename Hb into Hbodies end.
      eapply All_In in X as [X]; [|exact Hin]. cbn in X.
      eapply forallb_forall in Hbodies; [|exact Hin]. eapply X; eauto.
    - destruct s; simp compile; reflexivity.
    - rewrite !map_InP_spec.
      match goal with Hb : is_true (wf_fix _ _ _ _) |- _ => unfold wf_fix in Hb end. rtoProp.
      assert (Heq : map (fun d => let '(arg, expr) := force_lambda (compile Σ' (dbody d)) in
                       (local_name (string_of_name (dname d)), arg, expr)) m =
                    map (fun d => let '(arg, expr) := force_lambda (compile Σ (dbody d)) in
                       (local_name (string_of_name (dname d)), arg, expr)) m).
      { solve_all. unfold test_def in b0. now erewrite a. }
      now rewrite Heq.
    - destruct p as [? []]; simp compile; reflexivity.
  Qed.

  Context (Σ : global_declarations).
  Context (Hnpars : forall kn mdecl, lookup_env Σ kn = Some (InductiveDecl mdecl) -> ind_npars mdecl = 0).

  Lemma wf_of_wellformed Σ' k t :
    wellformed Σ' k t -> env_sub Σ' Σ -> wf Σ t.
  Proof.
    intros Hwf Hs. induction t in k, Hwf |- * using EInduction.term_forall_list_ind;
      cbn [wellformed] in Hwf; rtoProp; try solve [constructor; eauto].
    - match goal with Hi : is_true (isSome (lookup_constructor _ _ _)) |- _ => rename Hi into Hsome end.
      match goal with Hb : is_true (if cstr_as_blocks then _ else _) |- _ => rename Hb into Hblk end.
      destruct (lookup_constructor Σ' i n) as [[[mdecl idecl] cdecl]|] eqn:Hlc; cbn in Hsome; [|discriminate].
      rewrite Hblocks in Hblk. rtoProp.
      match goal with Hb : context [lookup_constructor_pars_args] |- _ => rename Hb into Hpa end.
      constructor.
      + intros mdecl' idecl' cdecl' Hlc'.
        rewrite (env_sub_lookup_constructor _ _ _ _ _ Hs Hlc) in Hlc'. injection Hlc' as <- <- <-.
        unfold lookup_constructor_pars_args in Hpa. rewrite Hlc in Hpa. cbn in Hpa.
        destruct (lookup_constructor_decompose _ _ _ _ _ _ Hlc) as [Hind _].
        unfold lookup_inductive, lookup_minductive in Hind.
        destruct (lookup_env Σ' (inductive_mind i)) as [[|m]|] eqn:He; cbn in Hind; try discriminate.
        destruct nth_error; cbn in Hind; [injection Hind as <- <-|discriminate].
        apply Hs in He as [He _]. rewrite (Hnpars _ _ He) in Hpa. apply eqb_eq in Hpa. cbn in Hpa. lia.
      + solve_all; try (eapply All_Forall; solve_all).
    - constructor; eauto. solve_all; try (eapply All_Forall; solve_all).
    - constructor. match goal with Hb : is_true (wf_fix _ _ _ _) |- _ => unfold wf_fix in Hb end.
      rtoProp. solve_all; try (eapply All_Forall; solve_all).
    - now rewrite Hprim in H.
    - now rewrite Hlazy in H.
    - now rewrite Hlazy in H.
  Qed.

  Lemma consts_of_wellformed Σ' k t kn :
    wellformed Σ' k t -> In kn (consts t) ->
    exists d body, lookup_env Σ' kn = Some (ConstantDecl d) /\ cst_body d = Some body.
  Proof.
    intros Hwf. induction t in k, Hwf |- * using EInduction.term_forall_list_ind;
      cbn [wellformed consts] in Hwf |- *; rtoProp; intros Hin; cbn [In] in Hin; try contradiction.
    - eauto.
    - apply in_app_iff in Hin as [|]; eauto.
    - apply in_app_iff in Hin as [|]; eauto.
    - destruct Hin as [<-|[]].
      destruct (lookup_constant Σ' s) as [d|] eqn:Hc; [|discriminate].
      unfold lookup_constant in Hc. destruct (lookup_env Σ' s) as [[]|] eqn:He; cbn in Hc; try discriminate.
      injection Hc as ->. rewrite Hax in H0. destruct (cst_body d) eqn:Hb; cbn in H0; [eauto|discriminate].
    - match goal with Hb : is_true (if cstr_as_blocks then _ else _) |- _ => rename Hb into Hblk end.
      rewrite Hblocks in Hblk. rtoProp.
      match goal with Hb : is_true (forallb _ args) |- _ => rename Hb into Hargs end.
      apply in_flat_map in Hin as (x & Hx & Hin).
      eapply All_In in X as [X]; [|exact Hx]. eapply X; eauto.
      eapply forallb_forall in Hargs; eauto.
    - match goal with Hb : is_true (forallb _ l) |- _ => rename Hb into Hbrs end.
      apply in_app_iff in Hin as [|Hin]; eauto.
      apply in_flat_map in Hin as (x & Hx & Hin).
      eapply All_In in X as [X]; [|exact Hx]. eapply X; eauto.
      eapply forallb_forall in Hbrs; eauto.
    - match goal with Hb : is_true (wf_fix _ _ _ _) |- _ => unfold wf_fix in Hb end. rtoProp.
      match goal with Hb : is_true (forallb _ m) |- _ => rename Hb into Hm end.
      apply in_flat_map in Hin as (x & Hx & Hin).
      eapply All_In in X as [X]; [|exact Hx]. eapply X; eauto.
      eapply forallb_forall in Hm; eauto.
  Qed.

  Definition consts_of (Σ' : global_declarations) : list kername :=
    flat_map (fun '(kn, d) => match d with
                               | ConstantDecl {| cst_body := Some _ |} => [kn]
                               | _ => []
                               end) Σ'.

  Lemma consts_of_In Σ' kn d body :
    lookup_env Σ' kn = Some (ConstantDecl d) -> cst_body d = Some body -> In kn (consts_of Σ').
  Proof.
    intros He%lookup_env_In' Hb. apply in_flat_map. exists (kn, ConstantDecl d). split; [exact He|].
    destruct d; cbn in *; subst. now left.
  Qed.

  Lemma consts_of_lookup Σ' kn :
    In kn (consts_of Σ') -> exists d, lookup_env Σ' kn = Some d.
  Proof.
    induction Σ' as [|[kn' d'] Σ' IH]; cbn; [tauto|].
    intros Hin. destruct (eqb_spec kn kn'); [eauto|].
    apply in_app_iff in Hin as [Hin|Hin]; [|auto].
    destruct d' as [[[]]|]; cbn in Hin; try tauto. destruct Hin as [->|[]]; congruence.
  Qed.

  Lemma decls_correct Σ' genv :
    wf_glob Σ' -> env_sub Σ' Σ ->
    eval_decls (initial_env Σ) (compile_env Σ') genv ->
    globals_rel Σ (consts_of Σ') (namespace.v _ genv).
  Proof.
    induction Σ' as [|[kn d] Σ' IH] in genv |- *; intros Hwf Hs Hev.
    - intros kn' ? ? ? [].
    - inversion Hwf as [|? ? ? Hwf' Hd Hfr]; subst.
      assert (Hs' : env_sub Σ' Σ) by (eapply env_sub_trans; [now apply env_sub_cons|exact Hs]).
      destruct d as [[[b|]]|mdecl]; cbn in Hev |- *.
      + inversion Hev as [|? ? genv' ? ? w Hev' Hw]; subst.
        specialize (IH genv' Hwf' Hs' Hev').
        cbn in Hd.
        intros kn' decl body v Hin Hdecl Hbody Heval.
        destruct (eqb_spec kn' kn) as [->|Hne].
        *
          destruct (Hs kn (ConstantDecl {| cst_body := Some b |})) as [Hl Hidx]; [cbn; now rewrite eqb_refl|].
          unfold declared_constant in Hdecl. rewrite Hl in Hdecl. injection Hdecl as <-.
          cbn in Hbody. injection Hbody as <-.
          assert (Hc : namespace.c _ genv' = ctor_env Σ) by (now rewrite (eval_decls_c _ _ _ Hev')).
          assert (Hwfb : wf Σ b) by (eapply wf_of_wellformed; eauto).
          destruct (compile_correct Σ [] b v Heval genv' Hwfb Hc) as (w' & Hw' & Hr).
          { intros ? ? Hl0; cbn in Hl0; discriminate Hl0. }
          { intros kn'' decl'' body'' v'' Hin'' ???.
            eapply IH; eauto. destruct (consts_of_wellformed _ _ _ _ Hd Hin'') as (d'' & b'' & He'' & Hb'').
            eapply consts_of_In; eauto. }
          rewrite <- (compile_sub _ _ _ _ Hd Hs') in Hw'.
          pose proof (evaluate_det _ _ _ _ Hw Hw') as [= <-].
          exists w. split; [|exact Hr].
          cbn [namespace.v]. rewrite nsLookup_nsBind.
          unfold global_name, global_ident. rewrite Hidx. cbn [global_index]. rewrite eqb_refl.
          now rewrite Strings.String.eqb_refl.
        *
          destruct Hin as [->|Hin]; [congruence|].
          destruct (IH kn' decl body v Hin) as (w' & Hl & Hr); auto.
          exists w'. split; [|exact Hr]. cbn [namespace.v]. rewrite nsLookup_nsBind.
          match goal with |- context [Strings.String.eqb ?a ?b] => destruct (Strings.String.eqb_spec a b) as [Heq|] end; [|exact Hl].
          exfalso. unfold global_name, global_ident in Heq.
          apply (global_ident_at_inj #|Σ'| (global_index Σ kn') kn kn') in Heq.
          destruct (consts_of_lookup _ _ Hin) as [d' Hd'].
          destruct (Hs' _ _ Hd') as [HdΣ Hidx]. rewrite Hidx in Heq.
          apply global_index_lt in Hd'. lia.
      + inversion Hev.
      + eapply IH; eauto.
  Qed.

  Theorem compile_program_correct t v genv :
    wf_glob Σ -> wellformed Σ 0 t ->
    EWcbvEvalNamed.eval Σ [] t v ->
    eval_decls (initial_env Σ) (compile_env Σ) genv ->
    exists w, evaluate genv (compile Σ t) (Rval w) /\ vrel Σ v w.
  Proof.
    intros Hwfg Hwft Hev Hdecls.
    apply (compile_correct Σ [] t v Hev genv).
    - eapply wf_of_wellformed; eauto. apply env_sub_refl.
    - rewrite (eval_decls_c _ _ _ Hdecls). reflexivity.
    - intros ? ? Hl0; cbn in Hl0; discriminate Hl0.
    - intros kn decl body v' Hin Hdecl Hbody Heval.
      eapply decls_correct; eauto; [apply env_sub_refl|].
      destruct (consts_of_wellformed _ _ _ _ Hwft Hin) as (d & b & He & Hb).
      eapply consts_of_In; eauto.
  Qed.

End Program.

Section FirstOrder.
  Context (Σ : global_declarations).

  Fixpoint compile_value (v : value) : val :=
    match v with
    | vConstruct ind c args =>
        match lookup_constructor Σ ind c with
        | Some (_, _, cdecl) => Conv (Some (TypeStamp (ctor_name c cdecl) 0)) (map compile_value args)
        | None => Litv (StrLit (String.to_string "constructor not found"))
        end
    | _ => Litv (StrLit (String.to_string "not a first-order value"))
    end.

  Inductive fo_value : value -> Prop :=
  | fo_vConstruct ind c args : Forall fo_value args -> fo_value (vConstruct ind c args).

  Fixpoint value_depth (v : value) : nat :=
    match v with
    | vConstruct _ _ args => S (list_max (map value_depth args))
    | _ => 0
    end.

  Lemma vrel_fo_depth n v w : value_depth v <= n -> fo_value v -> vrel Σ v w -> w = compile_value v.
  Proof.
    induction n in v, w |- *; intros Hd Hfo Hr; inversion Hfo as [ind c args Hfos]; subst; cbn in Hd; [lia|].
    inversion Hr as [? ? mdecl idecl cdecl ? ws Hlc Hargs| |]; subst.
    cbn [compile_value]. rewrite Hlc. f_equal.
    assert (Hds : forall x, In x args -> value_depth x <= n).
    { intros x Hx. enough (value_depth x <= list_max (map value_depth args)) by lia.
      clear -Hx. induction args as [|a args IH]; cbn in *; [tauto|].
      destruct Hx as [->|Hx]; [apply Nat.le_max_l|]. specialize (IH Hx).
      etransitivity; [exact IH|apply Nat.le_max_r]. }
    clear Hr Hlc Hd. induction Hargs as [|x y l l' Hxy Hl IHl]; cbn [map]; [reflexivity|].
    inversion Hfos as [|? ? Hx Hfos']; subst. f_equal.
    - apply IHn; auto. apply Hds. now left.
    - apply IHl; [constructor; exact Hfos'|exact Hfos'|intros z Hz; apply Hds; now right].
  Qed.

  Lemma vrel_fo v w : fo_value v -> vrel Σ v w -> w = compile_value v.
  Proof. apply (vrel_fo_depth (value_depth v)). lia. Qed.

End FirstOrder.
