From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From F_mu_ref_conc_sub Require Export rules typing.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.
Import uPred.

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapIG Σ}.
  Notation D := (valO F_mu_ref_conc_lang -n> iProp Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D → D.

  Program Definition env_lookup (x : var) : listO D -n> D := λne Δ,
    from_option id (cconst False)%I (Δ !! x).
  Solve Obligations with solve_proper.

  Definition interp_top : listO D -n> D := λne Δ w, True%I.

  Program Definition interp_unit : listO D -n> D := λne Δ w, ⌜w = UnitV⌝%I.
  Program Definition interp_nat : listO D -n> D := λne Δ w, ⌜∃ n, w = #nv n⌝%I.
  Program Definition interp_bool : listO D -n> D := λne Δ w, ⌜∃ n, w = #♭v n⌝%I.

  Program Definition interp_prod
      (interp1 interp2 : listO D -n> D) : listO D -n> D := λne Δ w,
    (∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ interp1 Δ w1 ∧ interp2 Δ w2)%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listO D -n> D) : listO D -n> D := λne Δ w,
    ((∃ w1, ⌜w = InjLV w1⌝ ∧ interp1 Δ w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∧ interp2 Δ w2))%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_arrow
      (interp1 interp2 : listO D -n> D) : listO D -n> D := λne Δ w,
    (□ ∀ v, interp1 Δ v → WP App (of_val w) (of_val v) {{ interp2 Δ }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_forall
      (interp_bound interp : listO D -n> D) : listO D -n> D := λne Δ w,
    (□ ∀ τi : D,
      ⌜∀ v, Persistent (τi v)⌝ → □ (∀ v, τi v -∗ interp_bound Δ v) → WP TApp (of_val w) {{ interp (τi :: Δ) }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_rec1
      (interp : listO D -n> D) (Δ : listO D) (τi : D) : D := λne w,
    (□ (∃ v, ⌜w = FoldV v⌝ ∧ ▷ interp (τi :: Δ) v))%I.

  Global Instance interp_rec1_contractive
    (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof. by solve_contractive. Qed.

  Lemma fixpoint_interp_rec1_eq (interp : listO D -n> D) Δ x :
    fixpoint (interp_rec1 interp Δ) x ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed.

  Program Definition interp_rec (interp : listO D -n> D) : listO D -n> D := λne Δ,
    fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper.
  Qed.

  Program Definition interp_ref_inv (l : loc) : D -n> iProp Σ := λne τi,
    (∃ v, l ↦ᵢ v ∗ τi v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listO D -n> D) : listO D -n> D := λne Δ w,
    (∃ l, ⌜w = LocV l⌝ ∧ inv (logN .@ l) (interp_ref_inv l (interp Δ)))%I.
  Solve Obligations with solve_proper.

  Fixpoint interp (τ : type) : listO D -n> D :=
    match τ return _ with
    | Top => interp_top
    | TUnit => interp_unit
    | TNat => interp_nat
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => env_lookup x
    | TForall σ τ' => interp_forall (interp σ) (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | Tref τ' => interp_ref (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : listO D) (vs : list val) : iProp Σ :=
    (⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Definition interp_expr (τ : type) (Δ : listO D) (e : expr) :
    iProp Σ := WP e {{ ⟦ τ ⟧ Δ }}%I.

  Class env_Persistent Δ :=
    env_persistent : Forall (λ τi, ∀ v, Persistent (τi v)) Δ.
  Global Instance env_persistent_nil : env_Persistent [].
  Proof. by constructor. Qed.
  Global Instance env_persistent_cons τi Δ :
    (∀ v, Persistent (τi v)) → env_Persistent Δ → env_Persistent (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance env_persistent_lookup Δ x v :
    env_Persistent Δ → Persistent (env_lookup x Δ v).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.
  Global Instance interp_persistent τ Δ v :
    env_Persistent Δ → Persistent (interp τ Δ v).
  Proof.
    revert v Δ; induction τ=> v Δ HΔ; simpl; try apply _.
    rewrite /Persistent fixpoint_interp_rec1_eq /interp_rec1 /= intuitionistically_into_persistently.
    by apply persistently_intro'.
  Qed.
  Global Instance interp_env_base_persistent Δ Γ vs :
  env_Persistent Δ → TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof.
    intros HΔ. revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vs :
    env_Persistent Δ → Persistent (⟦ Γ ⟧* Δ vs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi w /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
    - intros w; simpl; properness; auto. by apply IHτ.
      by apply (IHτ0 (_ :: _)).
    - intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi w /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (x - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. by rewrite (interp_weaken [] Δ1 Δ2 τ') . }
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
    - intros w; simpl; properness; auto. by apply IHτ. apply (IHτ0 (_ :: _)).
    - intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst Δ2 τ τ' v :
    ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vs : ⟦ Γ ⟧* Δ vs ⊢ ⌜length Γ = length vs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⟦ τ ⟧ Δ v.
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : ⟦ [] ⟧* Δ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vs τ v :
    ⟦τ :: Γ ⟧* Δ (v :: vs) ⊣⊢ ⟦ τ ⟧ Δ v ∗ ⟦ Γ ⟧* Δ vs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) (vs : list val) τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vs ⊣⊢ ⟦ Γ ⟧* Δ vs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.

  Definition interp_Tenv (Δ : listO D) (Ξ : list type) : iProp Σ:=
    (⌜length Δ = length Ξ⌝ ∧ ∀ x τ, ⌜Ξ !! x = Some τ⌝ →
                                    □ (∀ v, env_lookup x Δ v -∗ interp τ Δ v))%I.

  Lemma interp_Tenv_weaken Δ Ξ τ τi :
    □ (∀ v, τi v -∗ interp τ Δ v) ∧ interp_Tenv Δ Ξ
    ⊣⊢ interp_Tenv (τi :: Δ) (τ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ)).
  Proof.
    iSplit.
    - iIntros "#[Hτ [Hlen HΞ]]". iDestruct "Hlen" as %Hlen.
      iSplit.
      { rewrite /= fmap_length; auto. }
      iIntros (x σ Hσ) "!#". iIntros (v) "Hv".
      destruct x; simpl in *; simplify_eq.
      + rewrite (interp_weaken [] [τi] Δ τ _) /=.
        by iApply "Hτ".
      + rewrite list_lookup_fmap in Hσ.
        destruct (Ξ !! x) as [δ|]eqn:Hxeq; last done.
        simpl in *; simplify_eq.
        rewrite (interp_weaken [] [τi] Δ δ _) /=.
        iApply "HΞ"; eauto.
    - iIntros "#[Hlen HΞ]". iDestruct "Hlen" as %Hlen.
      iSplit.
      { iAlways. iIntros (v) "Hv".
        rewrite -(interp_weaken [] [τi] Δ τ _) /=.
        by iApply ("HΞ" $! 0). }
      iSplit.
      { rewrite /= fmap_length in Hlen; auto. }
      iIntros (x σ Hσ) "!#". iIntros (v) "Hv".
      rewrite -(interp_weaken [] [τi] Δ σ _) /=.
      iApply ("HΞ" $! (S x)); last done.
      rewrite /= list_lookup_fmap Hσ //.
  Qed.

  Lemma logrel_subtyp Δ Ξ τ τ' v :
    env_Persistent Δ →
    subtype Ξ τ τ' →
    interp_Tenv Δ Ξ ⊢ □ (interp τ Δ v -∗ interp τ' Δ v).
  Proof.
    iIntros (HΔ Hsb) "#HΞ".
    iIntros "!# #Hτ".
    iInduction Hsb as [] "IH" forall (Δ HΔ v) "HΞ Hτ"; simpl; auto.
    - iDestruct "HΞ" as "[% HΞ]".
      iApply ("HΞ" $! x); eauto.
    - iApply "IH1"; eauto.
      iAlways. iApply "IH"; eauto.
    - rewrite -/interp.
      iAlways. iIntros (w) "#Hw".
      iApply wp_wand_r; iSplitL.
      + iApply "Hτ". iApply "IH"; eauto.
      + iIntros (?) "#?"; iApply "IH1"; eauto.
    - rewrite -/interp.
      iAlways. iIntros (τi Hτi) "#Hτi".
      iApply wp_wand_r; iSplitL; first by iApply "Hτ"; eauto.
      iIntros (?) "#?"; iApply "IH"; eauto.
      + by iPureIntro; apply env_persistent_cons.
      + iAlways. rewrite -interp_Tenv_weaken; auto.
    - iLöb as "ILH" forall (v) "Hτ".
      rewrite (fixpoint_unfold (interp_rec1 ⟦ σ ⟧ Δ) v).
      rewrite (fixpoint_unfold (interp_rec1 ⟦ τ ⟧ Δ) v).
      simpl.
      iAlways.
      iDestruct "Hτ" as (w ?) "Hτ".
      iExists _; iSplit; first done.
      iNext.
      iSpecialize ("IH" $! (fixpoint (interp_rec1 ⟦ σ ⟧ Δ) ::
                            fixpoint (interp_rec1 ⟦ τ ⟧ Δ) :: Δ) with "[]").
      { iPureIntro.
        constructor; last constructor; last done.
        - intros; by apply (interp_persistent (TRec σ)).
        - intros; by apply (interp_persistent (TRec τ)). }
      iSpecialize ("IH" $! w with "[]").
      { iAlways.
        iDestruct "HΞ" as "[HΞ1 HΞ2]".
        iSplit.
        { rewrite /= fmap_length. by iDestruct "HΞ1" as %->. }
        iIntros (x ρ Hx).
        destruct x as [|[|x]]; simpl in *; simplify_eq; simpl.
        - change (fixpoint (interp_rec1 ⟦ σ ⟧ Δ)) with (⟦ TRec σ ⟧ Δ).
          iAlways. by iIntros (u) "#?"; iApply "ILH".
        - change (fixpoint (interp_rec1 ⟦ τ ⟧ Δ)) with (⟦ TRec τ ⟧ Δ).
          change (fixpoint (interp_rec1 ⟦ σ ⟧ Δ)) with (⟦ TRec σ ⟧ Δ).
          iAlways. by iIntros (u) "#?".
        - iAlways.
          rewrite list_lookup_fmap in Hx.
          iIntros (u) "Hu".
          destruct (Δ !! x) as [δ|] eqn:HΔx; rewrite HΔx; last done.
          destruct (Ξ !! x) as [δ'|] eqn:HΞx; last done.
          iSpecialize ("HΞ2" $! x δ' with "[]"); first done.
          rewrite HΔx; simpl.
          iSpecialize ("HΞ2" $! u with "Hu").
          simpl in *; simplify_eq.
          change (δ'.[ren (+2)]) with (δ'.[upn 0 (ren (+2))]).
          by rewrite (interp_weaken [] [_; _] _ _ _). }
      rewrite (interp_weaken [] [_] (_ :: _) _ _).
      rewrite (interp_weaken [_] [_] _ _ _).
      by iApply "IH".
  Qed.

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
