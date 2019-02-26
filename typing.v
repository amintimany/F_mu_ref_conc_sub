From F_mu_ref_conc_sub Require Export lang.

Inductive type :=
  | Top : type
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (σ : type) (τ : {bind 1 of type})
  | Tref (τ : type).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Inductive subtype : list type → type → type → Prop :=
| sbt_var Ξ x τ : Ξ !! x = Some τ → subtype Ξ (TVar x) τ
| sbt_refl Ξ τ : subtype Ξ τ τ
| sbt_trans Ξ τ1 τ2 τ3 : subtype Ξ τ1 τ2 → subtype Ξ τ2 τ3 → subtype Ξ τ1 τ3
| sbt_top Ξ τ : subtype Ξ τ Top
| sbt_arrow Ξ σ σ' τ τ' : subtype Ξ σ' σ → subtype Ξ τ τ' →
                        subtype Ξ (TArrow σ τ) (TArrow σ' τ')
| sbt_forall Ξ σ τ1 τ2 : subtype (σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ)) τ1 τ2 →
                         subtype Ξ (TForall σ τ1) (TForall σ τ2).

Fixpoint binop_res_type (op : binop) : type :=
  match op with
  | Add => TNat | Sub => TNat | Mult => TNat
  | Eq => TBool | Le => TBool | Lt => TBool
  end.

Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EQRef τ : EqType (Tref τ).

Reserved Notation "Ξ |ₜ Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Ξ Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Ξ |ₜ Γ ⊢ₜ Var x : τ
  | Unit_typed : Ξ |ₜ Γ ⊢ₜ Unit : TUnit
  | Nat_typed n : Ξ |ₜ Γ ⊢ₜ #n n : TNat
  | Bool_typed b : Ξ |ₜ Γ ⊢ₜ #♭ b : TBool
  | BinOp_typed op e1 e2 :
     Ξ |ₜ Γ ⊢ₜ e1 : TNat → Ξ |ₜ Γ ⊢ₜ e2 : TNat →
     Ξ |ₜ Γ ⊢ₜ BinOp op e1 e2 : binop_res_type op
  | Pair_typed e1 e2 τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e1 : τ1 → Ξ |ₜ Γ ⊢ₜ e2 : τ2 → Ξ |ₜ Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e : TProd τ1 τ2 → Ξ |ₜ Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Ξ |ₜ Γ ⊢ₜ e : TProd τ1 τ2 → Ξ |ₜ Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Ξ |ₜ Γ ⊢ₜ e : τ1 → Ξ |ₜ Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Ξ |ₜ Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Ξ |ₜ Γ ⊢ₜ e0 : TSum τ1 τ2 → Ξ |ₜ τ1 :: Γ ⊢ₜ e1 : τ3 →
     Ξ |ₜ τ2 :: Γ ⊢ₜ e2 : τ3 → Ξ |ₜ Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Ξ |ₜ Γ ⊢ₜ e0 : TBool → Ξ |ₜ Γ ⊢ₜ e1 : τ → Ξ |ₜ Γ ⊢ₜ e2 : τ →
     Ξ |ₜ Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed e τ1 τ2 :
     Ξ |ₜ TArrow τ1 τ2 :: τ1 :: Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ Rec e : TArrow τ1 τ2
  | Lam_typed e τ1 τ2 :
      Ξ |ₜ τ1 :: Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | LetIn_typed e1 e2 τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e1 : τ1 → Ξ |ₜ τ1 :: Γ ⊢ₜ e2 : τ2 → Ξ |ₜ Γ ⊢ₜ LetIn e1 e2 : τ2
  | Seq_typed e1 e2 τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e1 : τ1 → Ξ |ₜ Γ ⊢ₜ e2 : τ2 → Ξ |ₜ Γ ⊢ₜ Seq e1 e2 : τ2
  | App_typed e1 e2 τ1 τ2 :
     Ξ |ₜ Γ ⊢ₜ e1 : TArrow τ1 τ2 → Ξ |ₜ Γ ⊢ₜ e2 : τ1 → Ξ |ₜ Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e σ τ :
     σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ) |ₜ subst (ren (+1)) <$> Γ ⊢ₜ e : τ →
     Ξ |ₜ Γ ⊢ₜ TLam e : TForall σ τ
  | TApp_typed e σ τ τ' : Ξ |ₜ Γ ⊢ₜ e : TForall σ τ → subtype Ξ τ' σ →
      Ξ |ₜ Γ ⊢ₜ TApp e : τ.[τ'/]
  | TFold e τ : Ξ |ₜ Γ ⊢ₜ e : τ.[TRec τ/] → Ξ |ₜ Γ ⊢ₜ Fold e : TRec τ
  | TUnfold e τ : Ξ |ₜ Γ ⊢ₜ e : TRec τ → Ξ |ₜ Γ ⊢ₜ Unfold e : τ.[TRec τ/]
  | TFork e : Ξ |ₜ Γ ⊢ₜ e : TUnit → Ξ |ₜ Γ ⊢ₜ Fork e : TUnit
  | TAlloc e τ : Ξ |ₜ Γ ⊢ₜ e : τ → Ξ |ₜ Γ ⊢ₜ Alloc e : Tref τ
  | TLoad e τ : Ξ |ₜ Γ ⊢ₜ e : Tref τ → Ξ |ₜ Γ ⊢ₜ Load e : τ
  | TStore e e' τ : Ξ |ₜ Γ ⊢ₜ e : Tref τ → Ξ |ₜ Γ ⊢ₜ e' : τ →
      Ξ |ₜ Γ ⊢ₜ Store e e' : TUnit
  | TCAS e1 e2 e3 τ :
     EqType τ → Ξ |ₜ Γ ⊢ₜ e1 : Tref τ → Ξ |ₜ Γ ⊢ₜ e2 : τ → Ξ |ₜ Γ ⊢ₜ e3 : τ →
     Ξ |ₜ Γ ⊢ₜ CAS e1 e2 e3 : TBool
  | TSub e τ τ' : Ξ |ₜ Γ ⊢ₜ e : τ → subtype Ξ τ τ' → Ξ |ₜ Γ ⊢ₜ e : τ'
where "Ξ |ₜ Γ ⊢ₜ e : τ" := (typed Ξ Γ e τ).

(* Lemma typed_subst_invariant Ξ Γ e τ s1 s2 : *)
(*   Ξ |ₜ Γ ⊢ₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2]. *)
(* Proof. *)
(*   intros Htyped; revert s1 s2. *)
(*   assert (∀ x Γ, x < length (subst (ren (+1)) <$> Γ) → x < length Γ). *)
(*   { intros ??. by rewrite fmap_length. } *)
(*   assert (∀ {A} `{Ids A} `{Rename A} (s1 s2 : nat → A) x, *)
(*     (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x). *)
(*   { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal lia. } *)
(*   induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with lia. *)
(* Qed. *)
(* Lemma n_closed_invariant n (e : expr) s1 s2 : *)
(*   (∀ f, e.[upn n f] = e) → (∀ x, x < n → s1 x = s2 x) → e.[s1] = e.[s2]. *)
(* Proof. *)
(*   intros Hnc. specialize (Hnc (ren (+1))). *)
(*   revert n Hnc s1 s2. *)
(*   induction e => m Hmc s1 s2 H1; asimpl in *; try f_equal; *)
(*     try (match goal with H : _ |- _ => eapply H end; eauto; *)
(*          try inversion Hmc; try match goal with H : _ |- _ => by rewrite H end; *)
(*          fail). *)
(*   - apply H1. rewrite iter_up in Hmc. destruct lt_dec; try lia. *)
(*     asimpl in *. injection Hmc as Hmc. unfold var in *. omega. *)
(*   - unfold upn in *. *)
(*     change (e.[up (up (upn m (ren (+1))))]) with *)
(*     (e.[iter (S (S m)) up (ren (+1))]) in *. *)
(*     apply (IHe (S (S m))). *)
(*     + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
(*     + intros [|[|x]] H2; [by cbv|by cbv |]. *)
(*       asimpl; rewrite H1; auto with lia. *)
(*   - apply (IHe (S m)). *)
(*     + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
(*     + intros [|x] H2; [by cbv |]. *)
(*       asimpl; rewrite H1; auto with lia. *)
(*   - apply (IHe0 (S m)). *)
(*     + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
(*     + intros [|x] H2; [by cbv |]. *)
(*       asimpl; rewrite H1; auto with lia. *)
(*   - change (e1.[up (upn m (ren (+1)))]) with *)
(*     (e1.[iter (S m) up (ren (+1))]) in *. *)
(*     apply (IHe0 (S m)). *)
(*     + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
(*     + intros [|x] H2; [by cbv |]. *)
(*       asimpl; rewrite H1; auto with lia. *)
(*   - change (e2.[up (upn m (ren (+1)))]) with *)
(*     (e2.[upn (S m) (ren (+1))]) in *. *)
(*     apply (IHe1 (S m)). *)
(*     + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
(*     + intros [|x] H2; [by cbv |]. *)
(*       asimpl; rewrite H1; auto with lia. *)
(* Qed. *)

Fixpoint env_subst (vs : list val) : var → expr :=
  match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end.

Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs x = of_val v.
Proof.
  revert vs; induction x => vs.
  - by destruct vs; inversion 1.
  - destruct vs as [|w vs]; first by inversion 1.
    rewrite -lookup_tail /=.
    apply IHx.
Qed.

(* Lemma typed_n_closed Γ τ e : Γ ⊢ₜ e : τ → (∀ f, e.[upn (length Γ) f] = e). *)
(* Proof. *)
(*   intros H. induction H => f; asimpl; simpl in *; auto with f_equal. *)
(*   - apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia. *)
(*   - f_equal. apply IHtyped. *)
(*   - by f_equal; rewrite map_length in IHtyped. *)
(* Qed. *)

(** Weakening *)
(* Lemma context_gen_weakening ξ Γ' Γ e τ : *)
(*   Γ' ++ Γ ⊢ₜ e : τ → *)
(*   Γ' ++ ξ ++ Γ ⊢ₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ. *)
(* Proof. *)
(*   intros H1. *)
(*   remember (Γ' ++ Γ) as Ξ. revert Γ' Γ ξ HeqΞ. *)
(*   induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed. *)
(*   - rewrite iter_up; destruct lt_dec as [Hl | Hl]. *)
(*     + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H. *)
(*     + asimpl. constructor. rewrite lookup_app_r; auto with lia. *)
(*       rewrite lookup_app_r; auto with lia. *)
(*       rewrite lookup_app_r in H; auto with lia. *)
(*       match goal with *)
(*         |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia *)
(*       end. *)
(*   - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)). *)
(*   - constructor. by apply (IHtyped (_ :: _ :: _)). *)
(*   - constructor. by apply (IHtyped (_ :: _)). *)
(*   - econstructor; eauto. by apply (IHtyped2 (_::_)). *)
(*   - constructor. *)
(*     specialize (IHtyped *)
(*       (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)). *)
(*     asimpl in *. rewrite ?map_length in IHtyped. *)
(*     repeat rewrite fmap_app. apply IHtyped. *)
(*     by repeat rewrite fmap_app. *)
(* Qed. *)

(* Lemma context_weakening ξ Γ e τ : *)
(*   Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e.[(ren (+ (length ξ)))] : τ. *)
(* Proof. eapply (context_gen_weakening _ []). Qed. *)

(* Lemma closed_context_weakening ξ Γ e τ : *)
(*   (∀ f, e.[f] = e) → Γ ⊢ₜ e : τ → ξ ++ Γ ⊢ₜ e : τ. *)
(* Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed. *)
