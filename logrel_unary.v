From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From F_mu_ref_conc_sub Require Export rules typing.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.
Import uPred.

Definition logN : namespace := nroot .@ "logN".

Record domain_func (A B : ofeT) : Type := DomainFunc {
  domain_func_car :> A → B;
  domain_func_is_contractive : bool;
  domain_func_maybe_contractive :
    if domain_func_is_contractive then
      Contractive domain_func_car
    else
      NonExpansive domain_func_car
}.
Arguments DomainFunc {_ _} _ {_}.
Arguments domain_func_is_contractive {_ _} _.
Arguments domain_func_maybe_contractive {_ _} _.
Add Printing Constructor domain_func.
Global Instance domain_func_ne {A B} (f : domain_func A B) : NonExpansive f.
Proof.
  destruct f as [f [] Hf]; last done.
  by apply contractive_ne.
Qed.

Notation "'λdfne' x .. y , t" :=
  (@DomainFunc _ _ (λ x, .. (@DomainFunc _ _ (λ y, t) false _) ..) false _)
  (at level 200, x binder, y binder, right associativity).

Notation "'λdfco' x .. y , t" :=
  (@DomainFunc _ _ (λ x, .. (@DomainFunc _ _ (λ y, t) true _) ..) true _)
  (at level 200, x binder, y binder, right associativity).

Section domain_func.
  Context {A B : ofeT}.
  Global Instance ofe_contr_mor_proper
         (f : domain_func A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper; apply _. Qed.
  Instance domain_func_equiv : Equiv (domain_func A B) := λ f g, ∀ x, f x ≡ g x.
  Instance domain_func_dist : Dist (domain_func A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition domain_func_ofe_mixin : OfeMixin (domain_func A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure domain_funcO :=
    OfeT (domain_func A B) domain_func_ofe_mixin.

  Program Definition domain_func_chain (c : chain domain_funcO)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition domain_func_compl `{Cofe B} : Compl domain_funcO := λ c,
    λdfne x, compl (domain_func_chain c x).
  Next Obligation.
    intros ? c n x y Hx.
      by rewrite (conv_compl n (domain_func_chain c x))
                 (conv_compl n (domain_func_chain c y)) /= Hx.
  Qed.
  Global Program Instance domain_func_cofe `{Cofe B} : Cofe domain_funcO :=
    {| compl := domain_func_compl |}.
  Next Obligation.
    intros ? n c x; simpl.
    by rewrite (conv_compl n (domain_func_chain c x)) /=.
  Qed.

  Global Instance domain_func_mor_car_ne :
    NonExpansive2 (@domain_func_car A B).
  Proof. intros n f g Hfg x y Hx. rewrite Hx; apply Hfg. Qed.
  Global Program Instance domain_func_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@domain_func_car A B) := ne_proper_2 _.
  Lemma domain_func_ext (f g : domain_func A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End domain_func.

Arguments domain_funcO : clear implicits.

Notation "A -df> B" :=
  (domain_funcO A B) (at level 99, B at level 200, right associativity).

Instance ofe_contr_mor_inhabited {A B : ofeT} `{Inhabited B} :
  Inhabited (A -df> B) := populate (λdfne _, inhabitant).
Proof. solve_proper. Defined.

Program Definition cconst_contr {A B : ofeT} : B → A -df> B := λ x, λdfne _, x.
Next Obligation.
Proof. by intros ???????. Qed.

Record domain_mor (A : ofeT) Σ : Type := DomainMor {
  domain_mor_car :> A → iProp Σ;
  domain_mor_ne : NonExpansive domain_mor_car;
  domain_mor_persistent : ∀ x, Persistent (domain_mor_car x)
}.
Arguments DomainMor {_ _} _ {_}.
Arguments domain_mor_car {_ _} _.
Add Printing Constructor domain_mor.
Existing Instance domain_mor_ne.
Existing Instance domain_mor_persistent.

Notation "'λdo' x .. y , t" :=
  (@DomainMor _ _ (λ x, .. (@DomainMor _ _ (λ y, t) _ _) ..) _ _)
  (at level 200, x binder, y binder, right associativity).

Section domain_mor.
  Context {A : ofeT} {Σ : gFunctors}.
  Global Instance domain_mor_proper
         (f : domain_mor A Σ) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper; apply _. Qed.
  Instance domain_mor_equiv : Equiv (domain_mor A Σ) := λ f g, ∀ x, f x ≡ g x.
  Instance domain_mor_dist : Dist (domain_mor A Σ) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition domain_mor_ofe_mixin : OfeMixin (domain_mor A Σ).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure domain_morO :=
    OfeT (domain_mor A Σ) domain_mor_ofe_mixin.

  Local Arguments uPred_holds _ !_ _ _.

  Program Definition domain_mor_chain (c : chain domain_morO)
    (x : A) : chain (iProp Σ) := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition domain_mor_compl : Compl domain_morO := λ c,
    λdo x, compl (domain_mor_chain c x).
  Next Obligation.
    intros c n x y Hx.
      by rewrite (conv_compl n (domain_mor_chain c x))
                 (conv_compl n (domain_mor_chain c y)) /= Hx.
  Qed.
  Next Obligation. (* How can we prove this in the logic!? *)
  Proof.
    intros ??.
    constructor => n z Hz.
    unseal; rewrite /uPred_persistently_def /=.
    intros Hx.
    apply (conv_compl n (domain_mor_chain c x)); auto using cmra_core_validN.
    apply (symmetry (conv_compl n (domain_mor_chain c x))) in Hx;
      auto using cmra_core_validN.
    simpl in *.
    destruct (domain_mor_persistent _ _ (c n) x) as [Hpr].
    revert Hpr; unseal; intros Hpr.
    by apply Hpr.
  Qed.

  Global Program Instance domain_mor_cofe : Cofe domain_morO :=
    {| compl := domain_mor_compl |}.
  Next Obligation.
    intros n c x; simpl.
    by rewrite (conv_compl n (domain_mor_chain c x)) /=.
  Qed.


  Global Instance domain_mor_car_ne :
    NonExpansive2 (@domain_mor_car A Σ).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance domain_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@domain_mor_car A Σ) := ne_proper_2 _.
  Lemma dmain_mor_ext (f g : domain_mor A Σ) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End domain_mor.

Arguments domain_morO : clear implicits.

Notation "A -d> B" :=
  (domain_morO A B) (at level 99, B at level 200, right associativity).

Instance domain_mor_inhabited {A : ofeT} {Σ : gFunctors} :
  Inhabited (A -d> Σ) := populate (λdo _, inhabitant)%I.

Program Definition true_domain {A : ofeT} {Σ : gFunctors} : A -d> Σ := λdo _, True%I.

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapIG Σ}.
  Notation D := (valO F_mu_ref_conc_lang -d> Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -df> D.

  Program Definition make_contractive (interp : listO D -df> D) : listO D -df> D :=
    if domain_func_is_contractive interp then interp else
      λdfco Δ, λdo w, (▷ interp Δ w)%I.
  Next Obligation.
  Proof.
    intros interp n ????; simpl.
    apply later_contractive; destruct n; solve_proper.
  Qed.

  Global Instance make_contractive_contractive interp :
    Contractive (make_contractive interp).
  Proof.
    intros n ????.
    rewrite /make_contractive.
    destruct interp as [f [] Hf]; simpl in *.
    - by apply Hf.
    - apply later_contractive; destruct n; solve_proper.
  Qed.

  Program Definition env_lookup (x : var) : listO D -df> D :=
    λdfne Δ, from_option id true_domain (Δ !! x).
  Solve Obligations with simpl; solve_proper.

  Program Definition interp_top : listO D -df> D := λdfco Δ, true_domain.
  Next Obligation.
  Proof. simpl; apply const_contractive. Qed.

  Program Definition interp_unit : listO D -df> D := λdfco Δ, λdo w, (⌜w = UnitV⌝)%I.
  Next Obligation.
  Proof. done. Qed.

  Program Definition interp_nat : listO D -df> D := λdfco Δ, λdo w, (⌜∃ n, w = #nv n⌝)%I.
  Next Obligation.
  Proof. done. Qed.

  Program Definition interp_bool : listO D -df> D := λdfco Δ, λdo w, (⌜∃ n, w = #♭v n⌝)%I.
  Next Obligation.
  Proof. done. Qed.

  Program Definition interp_prod
      (interp1 interp2 : listO D -df> D) : listO D -df> D := λdfco Δ, λdo w,
    (▷ ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∧ interp1 Δ w1 ∧ interp2 Δ w2)%I.
  Next Obligation.
  Proof.
    intros ???????; simpl.
    apply later_contractive; destruct n; solve_proper.
  Qed.

  Program Definition interp_sum
      (interp1 interp2 : listO D -df> D) : listO D -df> D := λdfco Δ, λdo w,
    (▷ ((∃ w1, ⌜w = InjLV w1⌝ ∧ interp1 Δ w1) ∨
        (∃ w2, ⌜w = InjRV w2⌝ ∧ interp2 Δ w2)))%I.
  Next Obligation.
  Proof.
    intros ???????; simpl.
    apply later_contractive; destruct n; try solve_proper.
  Qed.

  Program Definition interp_arrow
      (interp1 interp2 : listO D -df> D) : listO D -df> D := λdfco Δ, λdo w,
    (▷ (((∃ f, ⌜w = RecV f⌝) ∨ (∃ f, ⌜w = LamV f⌝)) ∧
     □ ∀ v, interp1 Δ v → WP App (of_val w) (of_val v) {{ interp2 Δ }}))%I.
  Next Obligation.
  Proof.
    intros ???????; simpl.
    apply later_contractive; destruct n; try solve_proper.
  Qed.

  Program Definition interp_forall
      (interp_bound interp : listO D -df> D) : listO D -df> D := λdfco Δ, λdo w,
    (▷ ((∃ e, ⌜w = LamV e⌝) ∧
        (□ ∀ τi : D,
              ⌜∀ v, Persistent (τi v)⌝ → □ (∀ v, τi v -∗ interp_bound Δ v) →
                    WP TApp (of_val w) {{ interp (τi :: Δ) }})))%I.
  Next Obligation.
  Proof.
    intros ?????? Heq.
    apply later_contractive; destruct n; solve_proper.
  Qed.

  Program Definition interp_rec1
      (interp : listO D -df> D) (Δ : listO D) (τi : D) : D := λdo w,
    (□ (∃ v, ⌜w = FoldV v⌝ ∧ make_contractive interp (τi :: Δ) v))%I.

  Global Instance interp_rec1_contractive
    (interp : listO D -df> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof.
    intros ?????.
    rewrite /interp_rec1; simpl.
    apply intuitionistically_ne, exist_ne => ?.
    apply and_ne; first done.
    apply make_contractive_contractive.
    destruct n; first done; simpl in *.
    constructor; auto.
    apply Reflexive_instance_0; auto.
  Qed.

  Program Definition interp_rec (interp : listO D -df> D) : listO D -df> D :=
    λdfco Δ, λdo w, fixpoint (interp_rec1 interp Δ) w.
  Next Obligation.
    simpl.
    intros interp n ? ? Heq ?; simpl.
    rewrite fixpoint_unfold; simpl.
    symmetry.
    rewrite fixpoint_unfold; simpl.
    symmetry.
    apply intuitionistically_ne, exist_ne => ?.
    apply and_ne; auto.
    apply make_contractive_contractive.
    destruct n; first done; simpl in *.
    constructor; auto.
    apply fixpoint_ne => z u.
    rewrite /interp_rec1.
    apply intuitionistically_ne, exist_ne => ?.
    apply and_ne; auto.
    f_equiv.
    apply make_contractive_contractive.
    apply dist_dist_later.
    by constructor.
  Qed.

  Program Definition interp_ref
      (interp : listO D -df> D) : listO D -df> D := λdfco Δ, λdo w,
    (∃ l, ⌜w = LocV l⌝ ∧ inv (logN .@ l) (∃ v, l ↦ᵢ v ∗ (interp Δ) v))%I.
  Next Obligation.
  Proof.
    intros interp n ????; simpl.
    apply exist_ne => ?.
    apply and_ne; auto.
    apply inv_contractive.
    destruct n; solve_proper.
  Qed.

  Fixpoint interp (τ : type) : listO D -df> D :=
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

  Global Instance interp_env_base_persistent Δ Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof.
    revert vs. induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vs : Persistent (⟦ Γ ⟧* Δ vs) := _.

  Lemma interp_weaken' Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2)
    ∧ domain_func_is_contractive ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ =
      domain_func_is_contractive ⟦ τ ⟧.
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      intros ?; simpl; f_equiv.
      apply fixpoint_proper=> τi w /=.
      properness; auto.
      rewrite /make_contractive.
      destruct (IHτ (τi :: Δ1) Π Δ2) as [_ Hic].
      rewrite /= -fold_up_upn in Hic.
      rewrite Hic.
      destruct domain_func_is_contractive.
      + apply (IHτ (_ :: _)).
      + simpl; apply later_proper.
        apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      split; last done.
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ.
      by apply (IHτ0 (_ :: _)).
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof. apply interp_weaken'. Qed.

  Lemma trivial_subst n τ : upn n (τ .: ids) n = τ.[ren (+n)].
  Proof.
    induction n; asimpl; first done.
    by rewrite IHn; asimpl.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    valid_type τ →
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2)
  ∧  (domain_func_is_contractive ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ ≠
     domain_func_is_contractive ⟦ τ ⟧ →
    τ = TVar (length Δ1)).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2 Hvl; simpl; try (split; (auto || done)).
    - split; last done.
      destruct Hvl as [Hvl1 Hvl2].
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      destruct Hvl as [Hvl1 Hvl2].
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      destruct Hvl as [Hvl1 Hvl2].
      intros w; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - split; last done.
      destruct Hvl as [Hvl1 Hvl2].
      simpl in *.
      intros ?; simpl; f_equiv.
      apply fixpoint_proper=> τi w /=.
      properness; auto.
      rewrite /make_contractive.
      destruct
        (decide (domain_func_is_contractive
                   ⟦ τ.[up (upn (length Δ1) (τ' .: ids))] ⟧
                 = domain_func_is_contractive ⟦ τ ⟧)) as [->|Hneq].
      + destruct (domain_func_is_contractive ⟦ τ ⟧).
        * by apply (IHτ (_ :: _)).
        * apply later_proper. by apply (IHτ (_ :: _)).
      + by apply (IHτ (τi :: Δ1) Δ2) in Hneq; last done; subst.
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      split.
      + (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
        change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
        rewrite !lookup_app_r; [|lia ..].
        case EQ: (x - length Δ1) => [|n]; simpl.
        { symmetry. asimpl. by rewrite (interp_weaken [] Δ1 Δ2 τ'). }
        change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
        rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
      + match goal with
        | H : ¬ ?a < ?b |- _ => destruct (decide (a = b))
        end; first by simplify_eq.
        match goal with
        | H : ¬ ?a < ?b |- _ => destruct (a - b) eqn:Heq
        end; simpl; last done.
        unfold var in *; lia.
    - split; last done.
      destruct Hvl as [Hvl1 Hvl2].
      intros w; simpl; properness; auto. by apply IHτ. by apply (IHτ0 (_ :: _)).
    - split; last done.
      intros w; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst Δ2 τ τ' v :
    valid_type τ →
    ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. by intros; apply (interp_subst_up []). Qed.

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
    (⌜length Δ = length Ξ⌝ ∧
     ∀ x τ, ⌜Ξ !! x = Some τ⌝ → □ (∀ v, env_lookup x Δ v -∗ interp τ Δ v))%I.

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

  Lemma valid_rec_type τ :
    valid_type (TRec τ) → domain_func_is_contractive ⟦ τ ⟧ = true.
  Proof.
    simpl; destruct τ; simpl; tauto.
  Qed.

  Lemma logrel_subtyp Δ Ξ τ τ' v :
    subtype Ξ τ τ' →
    interp_Tenv Δ Ξ ⊢ □ (interp τ Δ v -∗ interp τ' Δ v).
  Proof.
    iIntros (Hsb) "#HΞ".
    iIntros "!# #Hτ".
    iInduction Hsb as [] "IH" forall (Δ v) "HΞ Hτ"; simpl; auto.
    - iDestruct "HΞ" as "[% HΞ]".
      iApply ("HΞ" $! x); eauto.
    - iApply "IH1"; eauto.
      iAlways. iApply "IH"; eauto.
    - rewrite -/interp.
      iDestruct "Hτ" as "[? Hτ]".
      iSplit; first done.
      iNext.
      iAlways.
      iIntros (w) "#Hw".
      iApply wp_wand_r; iSplitL.
      + iApply "Hτ". iApply "IH"; eauto.
      + iIntros (?) "#?"; iApply "IH1"; eauto.
    - rewrite -/interp.
      iNext.
      iDestruct "Hτ" as "[? Hτ]".
      iSplit; first done.
      iAlways. iIntros (τi Hτi) "#Hτi".
      iApply wp_wand_r; iSplitL; first by iApply "Hτ"; eauto.
      iIntros (?) "#?"; iApply "IH"; eauto.
      iAlways. rewrite -interp_Tenv_weaken; auto.
    - iLöb as "ILH" forall (v) "Hτ".
      rewrite -> (fixpoint_unfold (interp_rec1 ⟦ τ ⟧ Δ)).
      rewrite -> (fixpoint_unfold (interp_rec1 ⟦ σ ⟧ Δ)).
      simpl.
      iDestruct "Hτ" as (w Hw) "Hτ".
      iAlways.
      iExists _; iSplit; first done.
      rewrite /make_contractive !valid_rec_type //.
      iSpecialize ("IH" $! (fixpoint (interp_rec1 ⟦ σ ⟧ Δ)
                                     :: fixpoint (interp_rec1 ⟦ τ ⟧ Δ) :: Δ) w
                     with "[]").
      { iAlways.



      iApply ("IH").
      + iAlways.
        rewrite -(interp_Tenv_weaken _ _ (TRec _)).
        iSplit; last done.
        iAlways. iIntros (?) "? /=".
  Qed.

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr τ).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
