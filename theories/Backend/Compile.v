From Stdlib Require Import List String Arith Lia Cyclic.Int63.Uint63.
Import ListNotations.
From Equations Require Import Equations.
Import Logic.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring MRString.
From MetaRocq.Erasure Require Import EAst ESpineView EEtaExpanded EInduction ERemoveParams Erasure EGlobalEnv.

From CakeML Require Import ast namespace semanticPrimitives functions bigstep.

Open Scope bs.

Section Map2InP.
	Context {A1 A2 B : Type}.

Equations map2_InP (l1 : list A1) (l2 : list A2) (f : forall x1 x2, In x1 l1 -> In x2 l2 -> B) : list B :=
	map2_InP (cons x1 xs1) (cons x2 xs2) f := cons (f x1 x2 _ _) (map2_InP xs1 xs2 (fun x1 x2 inx1 inx2 => f x1 x2 _ _)) ;
    map2_InP _ _ f := nil.
End Map2InP.

Section MapiInP.
	Context {A B : Type}.

Equations mapi_InP (l : list A) (n : nat) (f : nat -> forall x : A, In x l -> B) : list B :=
	mapi_InP nil n _ := nil;
	mapi_InP (cons x xs) n f := cons (f n x _) (mapi_InP xs (S n) (fun n x inx => f n x _)).
End MapiInP.

Lemma mapi_InP_spec' {A B : Type} (f : nat -> A -> B) (l : list A) n :
	mapi_InP l n (fun n (x : A) _ => f n x) = mapi_rec f l n.
Proof.
  remember (fun n (x : A) _ => f n x) as g.
  funelim (mapi_InP l n g); simpl. reflexivity.
  simp mapi_InP.
  f_equal.
  now rewrite (H f0).
Qed.

Lemma mapi_InP_spec {A B : Type} (f : nat -> A -> B) (l : list A) :
  mapi_InP l 0 (fun n (x : A) _ => f n x) = mapi f l.
Proof.
  eapply mapi_InP_spec'.
Qed.

 Definition blocks_until i (num_args : list nat) :=
	#| filter (fun x => match x with 0 => false | _ => true end) (firstn i num_args)|.

 Definition nonblocks_until i num_args :=
    #| filter (fun x => match x with 0 => true | _ => false end) (firstn i num_args)|.

From MetaRocq Require Import EAst.

Section Compile.
	Context (Σ : global_declarations).

Definition lookup_record_projs (e : global_declarations) (ind : Kernames.inductive) : option (list Kernames.ident) :=
    match lookup_inductive e ind with
    | Some (mdecl, idecl) => Some (map proj_name idecl.(ind_projs))
    | None => None
    end.

Definition local_name (na : Kernames.ident) : String.string :=
  String.to_string ("v" ++ na).

Fixpoint global_index (Σ : global_declarations) (kn : Kernames.kername) : nat :=
  match Σ with
  | [] => 0
  | (kn', _) :: Σ' => if Kernames.eq_kername kn kn' then List.length Σ' else global_index Σ' kn
  end.

Definition global_ident_at (i : nat) (kn : Kernames.kername) : Kernames.ident :=
  "g" ++ MRString.string_of_nat i ++ "_" ++ Kernames.string_of_kername kn.

Definition global_ident (Σ : global_declarations) (kn : Kernames.kername) : Kernames.ident :=
  global_ident_at (global_index Σ kn) kn.

Definition global_name (Σ : global_declarations) (kn : Kernames.kername) : String.string :=
  String.to_string (global_ident Σ kn).

Definition ctor_ident (c : nat) (cdecl : constructor_body) : Kernames.ident :=
  "C" ++ MRString.string_of_nat c ++ "_" ++ MRString.string_of_nat cdecl.(cstr_nargs) ++ "_" ++ cdecl.(cstr_name).

Definition ctor_name (c : nat) (cdecl : constructor_body) : String.string :=
  String.to_string (ctor_ident c cdecl).

Definition lookup_constructor_names (e : global_declarations) (ind : Kernames.inductive) : option (list (String.string * nat)) :=
  match lookup_inductive e ind with
  | Some (mdecl, idecl) => Some (mapi (fun c cdecl => (ctor_name c cdecl, cdecl.(cstr_nargs))) idecl.(ind_ctors))
  | None => None
  end.

Definition case_pattern (name : String.string) (nargs : nat) (binders : list BasicAst.name) : pat :=
  let xs := map (fun x => local_name (BasicAst.string_of_name x)) binders in
  if andb (Nat.eqb (List.length xs) nargs) (ALL_DISTINCT _ Strings.String.eqb xs) then
    Pcon (Some (Short name)) (List.rev (map Pvar xs))
  else
    Pcon (Some (Short name)) (repeat Pany nargs).

 Definition lookup_constructor_args (e : global_declarations) (ind : Kernames.inductive) : option (list nat) :=
  match lookup_inductive e ind with
  | Some (mdecl, idecl) => Some (map cstr_nargs idecl.(ind_ctors))
  | None => None
  end.

Obligation Tactic := idtac.

Definition force_lambda (e : exp) :=
	match e with
	| Fun x e => (x,e)
	| _ => (String.to_string "__expanded",e) (* "__expanded" to replace by a free var of e*)
	end.

Notation Error s := (Raise (Lit( StrLit s))).

Equations? compile (t: term) : exp
	by wf t (fun x y : EAst.term => size x < size y) :=
	| tVar na => Var (Short (local_name na))
	| tLambda nm bod => Fun (local_name (BasicAst.string_of_name nm)) (compile bod)
	| tLetIn nm dfn bod =>
		Let (Some (local_name (BasicAst.string_of_name nm))) (compile dfn) (compile bod)
	| tApp fn arg =>
		App Opapp [compile fn;compile arg]
	| tConst nm => Var (Short (global_name Σ nm))
	| tConstruct i m args =>
		match lookup_constructor_names Σ i with
		| Some names_args => Con (Some (Short (fst (nth m names_args (String.to_string "", 0))))) (map_InP args (fun x (H : In x args) => compile x))
		| None => Error "error: inductive not found"
		end
	| tCase i mch brs =>
		match lookup_constructor_names Σ (fst i) with
		| Some names_args =>
			Mat (compile mch) (map2_InP names_args brs (fun '(name, nargs) '(binders, body) _ _ => (case_pattern name nargs binders, compile body)))
		| None => Error "error: inductive not found"
		end
	| tFix mfix idx =>
		let bodies :=
			map_InP mfix (fun d H =>
				let '(arg,expr) := force_lambda (compile d.(dbody)) in
					(local_name (BasicAst.string_of_name (d.(dname))), arg , expr)) in
			Letrec bodies (Var ( Short(fst (fst (nth idx bodies (String.to_string "", String.to_string "", Lit (StrLit "")))))))


	| tProj (Kernames.mkProjection ind _ nargs) bod => Raise (Lit( StrLit "inductive not found"))
	| tPrim (existT (EPrimitive.primIntModel i)) => Error "ignore for now"
	| tPrim (existT (EPrimitive.primFloatModel f)) =>  Error "ignore for now"
	| tPrim (existT (EPrimitive.primStringModel s)) => Error "ignore for now"
	| tPrim (existT (EPrimitive.primArrayModel a)) => Error  "ignore for now"
	| tLazy t => Raise (Lit( StrLit "error: tLazy not supported"))
	| tForce t =>  Raise (Lit( StrLit  "error: tForce not supported"))
	| tRel n => Raise (Lit( StrLit  "error: tRel has been translated away"))
	| tBox => Raise (Lit( StrLit "error: tBox has been translated away"))
	| tCoFix mfix idx => Raise (Lit( StrLit "error: tCofix not supported"))
	| tEvar _ _ => Raise (Lit( StrLit  "error: tEvar not supported")).
	Proof.
	all: try (cbn; lia).
		- simpl. clear compile. induction args.
			+ easy.
			+ inversion H.
				* simpl. rewrite H0. lia.
				* apply IHargs in H0.
					simpl.
					rewrite <- Nat.add_succ_l.
					rewrite <- Nat.add_succ_r.
					lia.
		- simpl. set (y:=(binders,body)).
			assert (body = snd y) by easy.
			rewrite H.
			rewrite <- Nat.add_succ_l.
			apply Nat.lt_lt_add_l.
			eapply (In_size snd size i1).
		- simpl. apply Nat.lt_lt_succ_r. eapply (In_size (fun x => dbody x) size H).
	Qed.

End Compile.

Definition compile_constant_decl Σ cb :=
	option_map (compile Σ) cb.(cst_body).

Fixpoint compile_env Σ : list (string * option exp) :=
	match Σ with
	| [] => []
	| (x,d) :: Σ => match d with
					ConstantDecl cb => (global_ident_at (List.length Σ) x, compile_constant_decl Σ cb) :: compile_env Σ
				| _ => compile_env Σ
				end
	end.

Definition compile_program (p : EProgram.eprogram) :=
	(compile_env (fst p), compile (fst p) (snd p)).
