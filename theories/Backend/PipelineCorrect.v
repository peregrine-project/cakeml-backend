(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICReduction PCUICAstUtils PCUICSN
    PCUICTyping PCUICProgram PCUICFirstorder PCUICEtaExpand.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EImplementBox EPretty Extract.
From MetaRocq Require Import ETransform EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EWcbvEvalNamed.
From MetaRocq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From CeresBS Require Import CeresSerialize.
Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).
From CakeML Require Import Pipeline.

Import EWcbvEval EWellformed.

Import Transform.Transform.

#[local] Arguments transform : simpl never.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.

#[local] Existing Instance extraction_normalizing.

From MetaRocq.Erasure Require Import EImplementBox EWellformed EProgram.

Lemma compile_value_box_mkApps x Σb args0:
compile_value_box Σb (PCUICAst.mkApps x args0) [] =
compile_value_box Σb x (map (fun v => compile_value_box Σb v []) args0).
Proof.
rewrite <- (app_nil_r (map _ _)).
generalize (@nil EAst.term) at 1 3. induction args0 using rev_ind; cbn.
- eauto.
- intros l. rewrite PCUICAstUtils.mkApps_nonempty; eauto.
  cbn. rewrite removelast_last last_last. rewrite IHargs0.
  destruct x; cbn; eauto.
  + do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.
  + destruct pcuic_lookup_inductive_pars; eauto.
    do 2 f_equal. repeat rewrite map_app. cbn. now repeat rewrite <- app_assoc.
Qed.

Fixpoint eval_fo (t: EAst.term) : EWcbvEvalNamed.value :=
  match t with
    | EAst.tConstruct ind c args => vConstruct ind c (map eval_fo args)
    | _ => vClos "" (EAst.tVar "error") []
  end.

Lemma implement_box_fo {efl : EWellformed.EEnvFlags} (Σ : global_env_ext_map) p :
  PCUICFirstorder.firstorder_value Σ [] p ->
  let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  v = implement_box v.
Proof.
  intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  v = implement_box v) _ _ H); intros. revert v.
  rewrite compile_value_box_mkApps. intro v. cbn in v. revert v.
  unfold pcuic_lookup_inductive_pars. rewrite PCUICExpandLetsCorrectness.trans_lookup.
  case_eq (lookup_env Σ (inductive_mind i)).
  2: { intro Hlookup; now rewrite Hlookup. }
  intros ? Hlookup; rewrite Hlookup. destruct g; eauto; simpl.
  rewrite <- map_skipn. set (map _ _). simpl. rewrite EImplementBox.implement_box_unfold_eq. simpl.
  f_equal. erewrite MRList.map_InP_spec. unfold l; clear l.
  eapply (Forall_skipn _ (ind_npars m)) in H1. revert H1. generalize (skipn (ind_npars m) args).
  induction 1; cbn; f_equal; eauto.
Qed.

Lemma represent_value_eval_fo (Σ : global_env_ext_map) p :
  PCUICFirstorder.firstorder_value Σ [] p ->
  let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  forall v', represents_value v' v -> v' = eval_fo v.
Proof.
  intro H. refine (PCUICFirstorder.firstorder_value_inds _ _ (fun p => let v := compile_value_box (PCUICExpandLets.trans_global_env Σ) p [] in
  forall v', represents_value v' v -> v' = eval_fo v) _ _ H); intros. revert H3.
  unfold v. clear v. rewrite compile_value_box_mkApps. cbn.
  unfold pcuic_lookup_inductive_pars. rewrite PCUICExpandLetsCorrectness.trans_lookup.
  case_eq (lookup_env Σ (inductive_mind i)).
  2: { intro Hlookup; now rewrite Hlookup. }
  intros ? Hlookup; rewrite Hlookup. destruct g; eauto; simpl.
  { inversion 1. }
  rewrite <- map_skipn. eapply (Forall_skipn _ (ind_npars m)) in H1.
  inversion 1; subst; eauto. f_equal. clear H3. revert vs H6 H1. generalize (skipn (ind_npars m) args).
  intros l vs Hvs Hl. eapply Forall_All in Hl. clear -Hl Hvs. revert vs Hvs.
  induction Hl; cbn; inversion 1; f_equal; subst.
  - eapply p; eauto.
  - eapply IHHl; eauto.
Qed.

From CakeML Require Import ast namespace semanticPrimitives bigstep Compile CompileCorrect.

Lemma fo_value_eval_fo Σb p :
  firstorder_evalue_block Σb p -> fo_value (eval_fo p).
Proof.
  intros H. eapply firstorder_evalue_block_elim with (P := fun p => fo_value (eval_fo p)); [|exact H].
  intros. cbn. constructor. eapply Forall_map. eapply Forall_impl; [exact H2|]. cbn. now intros ? [].
Qed.

Lemma wf_glob_npars {efl : EWellformed.EEnvFlags} (Σ : EAst.global_declarations) kn mdecl :
  EWellformed.has_cstr_params = false -> EWellformed.wf_glob efl Σ ->
  EGlobalEnv.lookup_env Σ kn = Some (EAst.InductiveDecl mdecl) -> EAst.ind_npars mdecl = 0.
Proof.
  intros Hp Hwf. induction Hwf as [|kn' d Σ Hwf IH Hd Hfr]; cbn; [discriminate|].
  destruct (eqb_spec kn kn') as [->|]; [|assumption].
  intros [= ->]. cbn in Hd. unfold EWellformed.wf_minductive in Hd. rewrite Hp in Hd.
  move/andP: Hd => [Hn _]. cbn in Hn. now apply eqb_eq in Hn.
Qed.

(** Compared to the [main] branch, the emitted program now starts with datatype
    declarations, and binders/constants keep their source names.  Hence:
    - the declarations are run by [eval_program_decls n0 env0], which first runs
      the [Dtype] blocks (allocating type stamps from [n0], extending [env0]) and
      then the [Dlet]s, instead of [eval_decls (initial_env N.1)];
    - [compile_value N.1 n0] uses the type stamps allocated from [n0];
    - the names used by the emitted program must not clash, which is checked by
      [names_ok N] (see CompileCorrect.v). *)
Lemma cakeml_correct_named (N : EProgram.eprogram) v n0 env0 genv :
  good_for_extraction named_extraction_env_flags_mlf N ->
  names_ok N = true ->
  ∥ EWcbvEvalNamed.eval N.1 [] N.2 v ∥ ->
  fo_value v ->
  eval_program_decls n0 env0 (compile_program N).1 genv ->
  evaluate genv (compile_program N).2 (Rval (compile_value N.1 n0 v)).
Proof.
  intros [Hwfg Hwft] Hnm [Hev] Hfo Hd.
  assert (Hprim : forall p : EPrimitive.prim_val EAst.term,
    @EWellformed.has_prim (@EWellformed.has_tPrim (@EWellformed.term_switches named_extraction_env_flags_mlf)) p = false).
  { intros [tag m]. now destruct tag. }
  assert (Hnp : forall kn mdecl, EGlobalEnv.lookup_env N.1 kn = Some (EAst.InductiveDecl mdecl) -> EAst.ind_npars mdecl = 0).
  { intros kn mdecl. now apply (wf_glob_npars (efl := named_extraction_env_flags_mlf)). }
  destruct N as [Σ t].
  destruct (@compile_program_correct named_extraction_env_flags_mlf eq_refl eq_refl Hprim eq_refl Σ Hnp n0 env0 t _ genv Hwfg Hwft Hnm Hev Hd)
    as (w & Hw & Hr).
  unfold compile_program; cbn [fst snd]. rewrite <- (vrel_fo Σ n0 _ _ _ Hfo Hr). exact Hw.
Qed.

(** The same statement for an arbitrary result value, related by [vrel]. *)
Lemma cakeml_correct_named_vrel (N : EProgram.eprogram) v n0 env0 genv :
  good_for_extraction named_extraction_env_flags_mlf N ->
  names_ok N = true ->
  ∥ EWcbvEvalNamed.eval N.1 [] N.2 v ∥ ->
  eval_program_decls n0 env0 (compile_program N).1 genv ->
  exists w, evaluate genv (compile_program N).2 (Rval w) /\
    vrel N.1 (namespace.c _ genv) (type_stamp n0 N.1) v w.
Proof.
  intros [Hwfg Hwft] Hnm [Hev] Hd.
  assert (Hprim : forall p : EPrimitive.prim_val EAst.term,
    @EWellformed.has_prim (@EWellformed.has_tPrim (@EWellformed.term_switches named_extraction_env_flags_mlf)) p = false).
  { intros [tag m]. now destruct tag. }
  assert (Hnp : forall kn mdecl, EGlobalEnv.lookup_env N.1 kn = Some (EAst.InductiveDecl mdecl) -> EAst.ind_npars mdecl = 0).
  { intros kn mdecl. now apply (wf_glob_npars (efl := named_extraction_env_flags_mlf)). }
  destruct N as [Σ t].
  exact (@compile_program_correct named_extraction_env_flags_mlf eq_refl eq_refl Hprim eq_refl Σ Hnp n0 env0 t _ genv Hwfg Hwft Hnm Hev Hd).
Qed.

Definition compile_named_value (Σ : global_env_ext_map) p :=
  eval_fo (compile_value_box (PCUICExpandLets.trans_global_env Σ) p []).

Section cakeml_pipeline_theorem.

  Variable Σ : global_env_ext_map.
  Variable HΣ : wf_ext Σ.
  Variable expΣ : expanded_global_env Σ.1.

  Variable t : term.
  Variable expt : expanded Σ.1 [] t.

  Variable v : term.

  Variable i : inductive.
  Variable u : Instance.t.
  Variable args : list term.

  Variable typing : ∥Σ ;;; [] |- t : mkApps (tInd i u) args∥.

  Variable fo : firstorder_ind Σ (firstorder_env Σ) i.

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Variable axfree : PCUICClassification.axiom_free Σ.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Let erased := transform (verified_erasure_pipeline default_erasure_config) (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation default_erasure_config).

  Variable Hgood : cakeml_check erased.

  Let named := transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation default_erasure_config).

  Lemma named_eq :
    named = (annotate_env [] (EImplementBox.implement_box_program erased).1,
             annotate [] (EImplementBox.implement_box_program erased).2).
  Proof.
    set (e := if cakeml_check erased >>> unsupported_msg then erased else unsupported_program).
    transitivity (annotate_env [] (EImplementBox.implement_box_program e).1,
                  annotate [] (EImplementBox.implement_box_program e).2); [reflexivity|].
    unfold e. rewrite Hgood. reflexivity.
  Qed.

  Let prog := @compile_malfunction_pipeline Σ t (mkApps (tInd i u) args) HΣ expΣ expt typing Normalisation.

  Lemma prog_eq : prog = compile_program named.
  Proof. reflexivity. Qed.

  Let Hpre := cakeml_check_spec erased (correctness (verified_erasure_pipeline default_erasure_config) (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation default_erasure_config)) Hgood.

  Lemma named_good : good_for_extraction named_extraction_env_flags_mlf named.
  Proof.
    rewrite named_eq. apply name_annotation_good_for_extraction.
    - now apply implement_box_good_for_extraction.
    - exact (proj2 (correctness implement_box_transformation erased Hpre)).
  Qed.

  Lemma named_eval : ∥ EWcbvEvalNamed.eval named.1 [] named.2 (compile_named_value Σ v) ∥.
  Proof.
    pose proof (verified_erasure_pipeline_theorem Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval default_erasure_config) as Hev.
    destruct (preservation implement_box_transformation erased _ Hpre Hev) as (v' & Hev' & Hobs).
    destruct (preservation name_annotation _ v' (correctness implement_box_transformation erased Hpre) Hev')
      as (vn & Hevn & Hobsn).
    assert (Hv' : v' = EImplementBox.implement_box (compile_value_box (PCUICExpandLets.trans_global_env Σ) v []))
      by exact Hobs.
    clear Hobs. rename Hv' into Hobs.
    change (∥ represents_value vn v' ∥) in Hobsn.
    change (∥ EWcbvEvalNamed.eval (annotate_env [] (EImplementBox.implement_box_program erased).1) []
               (annotate [] (EImplementBox.implement_box_program erased).2) vn ∥) in Hevn.
    rewrite named_eq. sq.
    unfold compile_named_value.
    assert (Hv : v' = compile_value_box (PCUICExpandLets.trans_global_env Σ) v []).
    { rewrite Hobs. symmetry. apply (@implement_box_fo extraction_env_flags_mlf Σ). eapply fo_v; eauto. }
    clear Hobs. subst v'. eapply represent_value_eval_fo in Hobsn; eauto.
    2:{ eapply fo_v; eauto. }
    now rewrite <- Hobsn.
  Qed.

  Variable Hnames : names_ok named = true.

  Theorem verified_cakeml_pipeline_theorem n0 env0 genv :
    eval_program_decls n0 env0 prog.1 genv ->
    evaluate genv prog.2 (Rval (compile_value named.1 n0 (compile_named_value Σ v))).
  Proof.
    rewrite prog_eq. apply cakeml_correct_named.
    - exact named_good.
    - exact Hnames.
    - exact named_eval.
    - unfold compile_named_value. eapply fo_value_eval_fo.
      eapply (verified_erasure_pipeline_firstorder_evalue_block Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval default_erasure_config).
  Qed.

End cakeml_pipeline_theorem.

(** The [main] branch also proves [verified_cakeml_plugin_theorem], which relates
    the plugin's [malfunction_pipeline default_malfunction_config] to
    [verified_named_erasure_pipeline].  On the MetaRocq 9.1 pipeline these use
    different erasure configurations ([safe_erasure_config] vs
    [default_erasure_config]) and the pipeline glue lemmas have to be redone, so
    that part is not ported yet. *)
