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

Fixpoint is_TVar τ :=
  match τ with
  | TVar _ => True
  | _ => False
  end.

Lemma is_TVar_up_ren n m τ : is_TVar τ ↔ is_TVar τ.[upn n (ren (+m))].
Proof.
  revert n m; induction τ; intros n m; simpl; auto; [].
  by rewrite iter_up; destruct lt_dec.
Qed.

Lemma valid_type_subst n σ τ : is_TVar τ.[upn n (σ .: ids)] → is_TVar τ.
Proof. by destruct τ. Qed.

Fixpoint valid_type (τ : type) :=
  match τ with
  | Top => True
  | TUnit => True
  | TNat => True
  | TBool => True
  | TProd τ1 τ2 => valid_type τ1 ∧ valid_type τ2
  | TSum τ1 τ2 => valid_type τ1 ∧ valid_type τ2
  | TArrow τ1 τ2 => valid_type τ1 ∧ valid_type τ2
  | TRec τ => (¬ is_TVar τ) ∧ valid_type τ
  | TVar x => True
  | TForall σ τ => valid_type σ ∧ valid_type τ
  | Tref τ => valid_type τ
  end.

Lemma valid_type_up_ren n m τ : valid_type τ → valid_type τ.[upn n (ren (+m))].
Proof.
  revert n m; induction τ; intros n m Hτ; simpl in *; try (by intuition auto).
  - destruct Hτ as [Hτ1 Hτ2].
    asimpl.
    split; last by auto.
    by rewrite -is_TVar_up_ren.
  - by rewrite iter_up; destruct lt_dec.
  - split; asimpl; intuition auto.
Qed.

Lemma valid_type_upn_subst n σ τ :
  valid_type σ → valid_type τ → valid_type τ.[upn n (σ .: ids)].
Proof.
  revert n σ; induction τ; intros n σ Hσ Hτ; simpl in *;  asimpl;
    try (by intuition auto).
  - destruct Hτ as [Hτ1 Hτ2]; split; last by auto.
    intros ?; apply Hτ1. eapply valid_type_subst; eauto.
  - rewrite iter_up; destruct lt_dec; first done.
    asimpl.
    match goal with
    | H : ¬ ?a < ?b |- _ => destruct (a - b)
    end; last done.
    asimpl.
    by apply (valid_type_up_ren 0).
Qed.

Inductive subtype : list type → type → type → Prop :=
| sbt_var Ξ x τ : valid_type τ → Ξ !! x = Some τ → subtype Ξ (TVar x) τ
| sbt_refl Ξ τ : subtype Ξ τ τ
| sbt_trans Ξ τ1 τ2 τ3 : subtype Ξ τ1 τ2 → subtype Ξ τ2 τ3 → subtype Ξ τ1 τ3
| sbt_top Ξ τ : valid_type τ → subtype Ξ τ Top
| sbt_arrow Ξ σ σ' τ τ' :
    subtype Ξ σ' σ → subtype Ξ τ τ' →
    subtype Ξ (TArrow σ τ) (TArrow σ' τ')
| sbt_forall Ξ σ τ1 τ2 :
    valid_type σ →
    subtype (σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ)) τ1 τ2 →
    subtype Ξ (TForall σ τ1) (TForall σ τ2)
|sbt_rec Ξ σ τ :
   valid_type (TRec σ) → valid_type (TRec τ) →
    subtype ((TVar 1) :: (TVar 1) :: (subst (ren (+2)) <$> Ξ))
            σ.[up (ren (+1))] τ.[ren (+1)] →
    subtype Ξ (TRec σ) (TRec τ).


Lemma subtype_valid Ξ σ τ : subtype Ξ σ τ → valid_type σ ↔ valid_type τ.
Proof.
  induction 1; simpl in *; intuition auto.
Qed.

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
  | Var_typed x τ : valid_type τ → Γ !! x = Some τ → Ξ |ₜ Γ ⊢ₜ Var x : τ
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
  | InjL_typed e τ1 τ2 :
      valid_type τ2 → Ξ |ₜ Γ ⊢ₜ e : τ1 → Ξ |ₜ Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 :
      valid_type τ1 → Ξ |ₜ Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Ξ |ₜ Γ ⊢ₜ e0 : TSum τ1 τ2 → Ξ |ₜ τ1 :: Γ ⊢ₜ e1 : τ3 →
     Ξ |ₜ τ2 :: Γ ⊢ₜ e2 : τ3 → Ξ |ₜ Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Ξ |ₜ Γ ⊢ₜ e0 : TBool → Ξ |ₜ Γ ⊢ₜ e1 : τ → Ξ |ₜ Γ ⊢ₜ e2 : τ →
     Ξ |ₜ Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed e τ1 τ2 :
      valid_type τ1 →
     Ξ |ₜ TArrow τ1 τ2 :: τ1 :: Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ Rec e : TArrow τ1 τ2
  | Lam_typed e τ1 τ2 :
      valid_type τ1 → Ξ |ₜ τ1 :: Γ ⊢ₜ e : τ2 → Ξ |ₜ Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | LetIn_typed e1 e2 τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e1 : τ1 → Ξ |ₜ τ1 :: Γ ⊢ₜ e2 : τ2 → Ξ |ₜ Γ ⊢ₜ LetIn e1 e2 : τ2
  | Seq_typed e1 e2 τ1 τ2 :
      Ξ |ₜ Γ ⊢ₜ e1 : τ1 → Ξ |ₜ Γ ⊢ₜ e2 : τ2 → Ξ |ₜ Γ ⊢ₜ Seq e1 e2 : τ2
  | App_typed e1 e2 τ1 τ2 :
     Ξ |ₜ Γ ⊢ₜ e1 : TArrow τ1 τ2 → Ξ |ₜ Γ ⊢ₜ e2 : τ1 → Ξ |ₜ Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e σ τ :
      valid_type σ →
     σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ) |ₜ subst (ren (+1)) <$> Γ ⊢ₜ e : τ →
     Ξ |ₜ Γ ⊢ₜ TLam e : TForall σ τ
  | TApp_typed e σ τ τ' :
      valid_type σ →
      Ξ |ₜ Γ ⊢ₜ e : TForall σ τ → subtype Ξ τ' σ →
      Ξ |ₜ Γ ⊢ₜ TApp e : τ.[τ'/]
  | TFold e τ :
      valid_type (TRec τ) → Ξ |ₜ Γ ⊢ₜ e : τ.[TRec τ/] → Ξ |ₜ Γ ⊢ₜ Fold e : TRec τ
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

Lemma typed_valid Ξ Γ e τ : Ξ |ₜ Γ ⊢ₜ e : τ → valid_type τ.
Proof.
  induction 1; simpl in *; intuition auto.
  - match goal with op : binop |- _ => by destruct op end.
  - apply (valid_type_upn_subst 0); auto.
    by rewrite subtype_valid; last by eauto.
  - by apply (valid_type_upn_subst 0).
  - rewrite -subtype_valid; eauto.
Qed.
