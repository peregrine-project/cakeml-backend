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

Lemma cakeml_correct_named (N : EProgram.eprogram) v genv :
  good_for_extraction named_extraction_env_flags_mlf N ->
  ∥ EWcbvEvalNamed.eval N.1 [] N.2 v ∥ ->
  fo_value v ->
  eval_decls (initial_env N.1) (compile_program N).1 genv ->
  evaluate genv (compile_program N).2 (Rval (compile_value N.1 v)).
Proof.
  intros [Hwfg Hwft] [Hev] Hfo Hd.
  assert (Hprim : forall p : EPrimitive.prim_val EAst.term,
    @EWellformed.has_prim (@EWellformed.has_tPrim (@EWellformed.term_switches named_extraction_env_flags_mlf)) p = false).
  { intros [tag m]. now destruct tag. }
  assert (Hnp : forall kn mdecl, EGlobalEnv.lookup_env N.1 kn = Some (EAst.InductiveDecl mdecl) -> EAst.ind_npars mdecl = 0).
  { intros kn mdecl. now apply (wf_glob_npars (efl := named_extraction_env_flags_mlf)). }
  destruct (@compile_program_correct named_extraction_env_flags_mlf eq_refl eq_refl Hprim eq_refl N.1 Hnp N.2 _ genv Hwfg Hwft Hev Hd)
    as (w & Hw & Hr).
  rewrite <- (vrel_fo _ _ _ Hfo Hr). exact Hw.
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

  Let erased := transform verified_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation).

  Variable Hgood : cakeml_check erased.

  Let named := transform verified_named_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation).

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

  Let Hpre := cakeml_check_spec erased (correctness verified_erasure_pipeline (Σ, t) (precond _ _ _ _ expΣ expt typing Normalisation)) Hgood.

  Lemma named_good : good_for_extraction named_extraction_env_flags_mlf named.
  Proof.
    rewrite named_eq. apply name_annotation_good_for_extraction.
    - now apply implement_box_good_for_extraction.
    - exact (proj2 (correctness implement_box_transformation erased Hpre)).
  Qed.

  Lemma named_eval : ∥ EWcbvEvalNamed.eval named.1 [] named.2 (compile_named_value Σ v) ∥.
  Proof.
    pose proof (verified_erasure_pipeline_theorem Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval) as Hev.
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

  Theorem verified_cakeml_pipeline_theorem genv :
    eval_decls (initial_env named.1) prog.1 genv ->
    evaluate genv prog.2 (Rval (compile_value named.1 (compile_named_value Σ v))).
  Proof.
    rewrite prog_eq. apply cakeml_correct_named.
    - exact named_good.
    - exact named_eval.
    - unfold compile_named_value. eapply fo_value_eval_fo.
      eapply (verified_erasure_pipeline_firstorder_evalue_block Σ HΣ expΣ t expt axfree v i u args Normalisation typing fo Heval).
  Qed.

End cakeml_pipeline_theorem.

From Stdlib Require Import ProofIrrelevance.
From MetaRocq.Erasure Require Import EReorderCstrs EEnvMap.

#[local] Arguments transform : simpl nomatch.

Lemma transform_compose_eq
  {env env' env'' term term' term'' value value' value'' : Type} {eval eval' eval''}
  (o : t env env' term term' value value' eval eval')
  (o' : t env' env'' term' term'' value' value'' eval' eval'')
  (prec : forall p, post o p -> pre o' p) x p1 :
  transform (compose o o' prec) x p1 = transform o' (transform o x p1) (prec _ (correctness o x p1)).
Proof. reflexivity. Qed.

Lemma transform_irr {env env' term term' value value' : Type} {eval eval'}
  (o : t env env' term term' value value' eval eval') x x' p p' :
  x = x' -> transform o x p = transform o x' p'.
Proof. intros ->. f_equal. apply proof_irrelevance. Qed.

Lemma pre_erasure_pipeline_mapping_nil p pr pr' :
  transform pre_erasure_pipeline_mapping ([], p) pr = ([], transform pre_erasure_pipeline p pr').
Proof.
  unfold pre_erasure_pipeline_mapping, pre_erasure_pipeline. cbv zeta.
  rewrite !transform_compose_eq.
  cbn [transform build_template_program_env_mapping eta_expand_mapping template_to_pcuic_mapping fst snd].
  f_equal; repeat apply transform_irr; reflexivity.
Qed.
Lemma reorder_nil t : EReorderCstrs.reorder [] t = t.
Proof.
  induction t using EInduction.term_forall_list_ind; simp reorder; cbn; f_equal; try solve_all.
Qed.

Lemma reorder_env_nil Σ : EReorderCstrs.reorder_env [] Σ = Σ.
Proof.
  induction Σ as [|[kn []] Σ IH]; cbn; f_equal; auto.
  - unfold reorder_decl, reorder_constant_decl. cbn. destruct c as [[]]; cbn; now rewrite ?reorder_nil.
  - unfold reorder_decl, reorder_inductive_decl. cbn. destruct m as [fin npars bodies]; cbn.
    do 3 f_equal. generalize 0. induction bodies; cbn; intros; f_equal; auto.
Qed.

Lemma optional_unsafe_transforms_safe p pr :
  transform (optional_unsafe_transforms safe_erasure_config) p pr = p.
Proof.
  unfold optional_unsafe_transforms. cbv zeta.
  rewrite !transform_compose_eq. reflexivity.
Qed.

Lemma rebuild_wf_env_eq {efl} q q' h h' : q = q' -> @rebuild_wf_env efl q h = @rebuild_wf_env efl q' h'.
Proof. intros ->. f_equal. apply proof_irrelevance. Qed.

Lemma erase_transform_make {guard : PCUICWfEnvImpl.abstract_guard_impl} p pr :
  (transform erase_transform p pr).1 =
    GlobalContextMap.make (transform erase_transform p pr).1.(GlobalContextMap.global_decls)
      (GlobalContextMap.wf (transform erase_transform p pr).1).
Proof.
  unfold erase_transform. cbn [transform]. unfold erase_program, erase_pcuic_program. cbn [fst GlobalContextMap.global_decls].
  apply GlobalContextMap.make_irrel.
Qed.

Lemma rebuild_reorder_nil {efl} (X : inductives_mapping * eprogram_env) Y fr h :
  X = ([], Y) -> Y.1 = GlobalContextMap.make Y.1.(GlobalContextMap.global_decls) fr ->
  @rebuild_wf_env efl (reorder_program X.1 (to_program X.2)) h = Y.
Proof.
  intros -> HY. destruct Y as [g t]. cbn in *. unfold rebuild_wf_env, reorder_program. cbn.
  match goal with |- (GlobalContextMap.make _ ?pf, _) = _ => generalize pf end.
  change (map (reorder_decl []) (GlobalContextMap.global_decls g)) with (reorder_env [] (GlobalContextMap.global_decls g)).
  rewrite reorder_env_nil reorder_nil. intros pf. f_equal.
  transitivity (GlobalContextMap.make g fr); [apply GlobalContextMap.make_irrel|now symmetry].
Qed.

Lemma verified_erasure_pipeline_mapping_nil {guard : PCUICWfEnvImpl.abstract_guard_impl} p pr pr' :
  transform verified_erasure_pipeline_mapping ([], p) pr = transform verified_erasure_pipeline p pr'.
Proof.
  unfold verified_erasure_pipeline_mapping, verified_erasure_pipeline. cbv zeta.
  rewrite transform_compose_eq. symmetry. rewrite transform_compose_eq. symmetry.
  unfold verified_lambdabox_pipeline_mapping. rewrite transform_compose_eq.
  apply transform_irr.
  rewrite transform_compose_eq. cbn [transform reorder_cstrs_transformation rebuild_wf_env_transform].
  eapply rebuild_reorder_nil.
  - rewrite transform_compose_eq. symmetry. rewrite transform_compose_eq. symmetry.
    cbn [transform pcuic_expand_lets_transform_mapping erase_transform_mapping fst snd].
    f_equal; repeat apply transform_irr; reflexivity.
  - exact (erase_transform_make _ _).
Qed.

Lemma switchable_erasure_pipeline_safe X p h pr' :
  X = ([], p) ->
  transform (switchable_erasure_pipeline safe_erasure_config) X h = transform verified_erasure_pipeline p pr'.
Proof.
  intros ->. unfold switchable_erasure_pipeline. cbn [enable_typed_erasure safe_erasure_config].
  rewrite transform_compose_eq optional_unsafe_transforms_safe.
  apply verified_erasure_pipeline_mapping_nil.
Qed.

Lemma malfunction_pipeline_default p pr pr1 pr2 :
  transform (malfunction_pipeline default_malfunction_config) ([], p) pr =
  transform verified_malfunction_pipeline (transform pre_erasure_pipeline p pr1) pr2.
Proof.
  unfold malfunction_pipeline, verified_malfunction_pipeline, verified_named_erasure_pipeline.
  rewrite transform_compose_eq. symmetry. rewrite transform_compose_eq. symmetry.
  apply transform_irr.
  rewrite transform_compose_eq. symmetry. rewrite transform_compose_eq. symmetry.
  apply transform_irr.
  rewrite transform_compose_eq.
  apply switchable_erasure_pipeline_safe.
  apply pre_erasure_pipeline_mapping_nil.
Qed.

Lemma erased_pre q : post verified_erasure_pipeline q -> pre post_verified_named_erasure_pipeline q.
Proof. cbn. intuition auto. Qed.

Section cakeml_plugin_theorem.

  Variable p : Ast.Env.program.

  Variable pr : pre (malfunction_pipeline default_malfunction_config) ([], p).

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Let pre_pr : pre pre_erasure_pipeline p := proj2 pr.

  Let pcuic := transform pre_erasure_pipeline p pre_pr.

  Let erased := transform erasure_pipeline p pre_pr.

  Let named := transform post_verified_named_erasure_pipeline erased
                 (erased_pre _ (correctness erasure_pipeline p pre_pr)).

  Let prog := run (malfunction_pipeline default_malfunction_config) ([], p) pr.

  Variable v : term.
  Variable i : inductive.
  Variable u : Instance.t.
  Variable args : list term.

  Variable typing : ∥ pcuic.1 ;;; [] |- pcuic.2 : mkApps (tInd i u) args ∥.

  Variable fo : firstorder_ind pcuic.1 (firstorder_env pcuic.1) i.

  Variable axfree : PCUICClassification.axiom_free pcuic.1.

  Variable Heval : ∥ PCUICWcbvEval.eval pcuic.1 pcuic.2 v ∥.

  Variable Hgood : cakeml_check erased.

  Theorem verified_cakeml_plugin_theorem genv :
    eval_decls (initial_env named.1) prog.1 genv ->
    evaluate genv prog.2 (Rval (compile_value named.1 (compile_named_value pcuic.1 v))).
  Proof.
    destruct (correctness pre_erasure_pipeline p pre_pr) as [[[HΣ _]] [[expΣ expt] _]].
    set (pre_v := precond pcuic.1 pcuic.2 _ HΣ expΣ expt typing Normalisation).
    assert (Her : erased = transform verified_erasure_pipeline (pcuic.1, pcuic.2) pre_v).
    { unfold erased, erasure_pipeline. rewrite transform_compose_eq. now apply transform_irr. }
    assert (Hgood' := Hgood). rewrite Her in Hgood'.
    pose proof (verified_cakeml_pipeline_theorem pcuic.1 HΣ expΣ pcuic.2 expt v i u args typing fo
                  Normalisation axfree Heval Hgood' genv) as H.
    assert (Hn : named = transform verified_named_erasure_pipeline (pcuic.1, pcuic.2) pre_v).
    { unfold verified_named_erasure_pipeline. rewrite transform_compose_eq.
      unfold named. apply transform_irr. exact Her. }
    assert (Hp : prog = compile_malfunction_pipeline expΣ expt typing).
    { unfold prog, run, time, compile_malfunction_pipeline.
      rewrite (malfunction_pipeline_default p pr pre_pr (precond _ _ _ HΣ expΣ expt typing Normalisation)).
      now apply transform_irr. }
    rewrite Hn Hp. exact H.
  Qed.

End cakeml_plugin_theorem.
