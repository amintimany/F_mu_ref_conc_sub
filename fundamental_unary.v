From F_mu_ref_conc_sub Require Export logrel_unary.
From F_mu_ref_conc_sub Require Import rules.
From iris.base_logic Require Export invariants.
From iris.program_logic Require Export lifting.
From iris.proofmode Require Import tactics.

Definition log_typed `{heapIG Σ} (Ξ Γ : list type) (e : expr) (τ : type) := ∀ Δ vs,
  env_Persistent Δ →
  interp_Tenv Δ Ξ -∗ ⟦ Γ ⟧* Δ vs -∗ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Ξ | Γ ⊨ e : τ" := (log_typed Ξ Γ e τ) (at level 74, e, τ at next level).

Section typed_interp.
  Context `{heapIG Σ}.
  Notation D := (valC -n> iProp Σ).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

  Theorem fundamental Ξ Γ e τ : Ξ |ₜ Γ ⊢ₜ e : τ → Ξ | Γ ⊨ e : τ.
  Proof.
    induction 1; iIntros (Δ vs HΔ) "#HΞ #HΓ /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
      erewrite env_subst_lookup; eauto.
        by iApply wp_value.
    - (* unit *) iApply wp_value; trivial.
    - (* nat *) iApply wp_value; simpl; eauto.
    - (* bool *) iApply wp_value; simpl; eauto.
    - (* nat bin op *)
      smart_wp_bind (BinOpLCtx _ e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (BinOpRCtx _ v) v' "# Hv'" IHtyped2.
      iDestruct "Hv" as (n) "%"; iDestruct "Hv'" as (n') "%"; simplify_eq/=.
      iApply wp_pure_step_later; auto. iNext. iApply wp_value.
      destruct op; simpl; try destruct eq_nat_dec;
        try destruct le_dec; try destruct lt_dec; eauto 10.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHtyped2.
      iApply wp_value; eauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped2 Δ (w :: vs)); auto. iApply interp_env_cons; auto.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped3 Δ (w :: vs)); auto. iApply interp_env_cons; auto.
    - (* If *)
      smart_wp_bind (IfCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct "Hv" as ([]) "%"; subst; simpl;
        [iApply wp_pure_step_later .. ]; auto; iNext;
      [iApply IHtyped2| iApply IHtyped3]; auto.
    - (* Rec *)
      iApply wp_value. simpl. iAlways. iLöb as "IH". iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
      iApply (IHtyped Δ (_ :: w :: vs)); auto.
      iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
    - (* Lam *)
      iApply wp_value. simpl. iAlways. iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl.
      iApply (IHtyped Δ (w :: vs)); auto.
      iApply interp_env_cons; iSplit; auto.
    - (* LetIn *)
      smart_wp_bind (LetInCtx _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. iApply (IHtyped2 Δ (v :: vs)); auto.
      iApply interp_env_cons; iSplit; eauto.
    - (* Seq *)
      smart_wp_bind (SeqCtx _) v "#Hv" IHtyped1; cbn.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      by iApply IHtyped2.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHtyped2.
      by iApply "Hv".
    - (* TLam *)
      iApply wp_value; simpl.
      iAlways; iIntros (τi) "% #Hτi".
      iApply wp_pure_step_later; auto; iNext.
      iApply IHtyped. rewrite -interp_Tenv_weaken; auto.
      by iApply interp_env_ren.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (⟦ τ' ⟧ Δ));
                                  [iPureIntro; apply _|]|]; cbn.
      { iAlways; iIntros (?); iApply (logrel_subtyp with "[]"); eauto. }
      iIntros (w) "?". by iApply interp_subst.
    - (* Fold *)
      iApply (wp_bind (fill [FoldCtx]));
        iApply wp_wand_l; iSplitL; [|iApply (IHtyped Δ vs); auto].
      iIntros (v) "#Hv". iApply wp_value.
      rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
      iAlways; eauto.
    - (* Unfold *)
      iApply (wp_bind (fill [UnfoldCtx]));
        iApply wp_wand_l; iSplitL; [|iApply IHtyped; auto].
      iIntros (v) "#Hv". rewrite /= fixpoint_interp_rec1_eq.
      change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
      iDestruct "Hv" as (w) "#[% Hw]"; subst.
      iApply wp_pure_step_later; cbn; auto using to_of_val.
      iNext. iApply wp_value. by iApply interp_subst.
    - (* Fork *)
      iApply wp_fork. rewrite -bi.later_sep. iNext; iSplitL; trivial.
      iApply wp_wand_l. iSplitL; [|iApply IHtyped; auto]; auto.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHtyped; cbn. iClear "HΓ". iApply wp_fupd.
      iApply wp_alloc; auto 1 using to_of_val.
      iNext; iIntros (l) "Hl".
      iMod (inv_alloc _ with "[Hl]") as "HN";
        [| iModIntro; iExists _; iSplit; trivial]; eauto.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHtyped; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iApply wp_atomic.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_load with "Hw1").
      iModIntro. iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHtyped2; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iApply wp_atomic.
      iInv (logN .@ l) as (z) "[Hz1 #Hz2]" "Hclose".
      iApply (wp_store with "Hz1"); auto using to_of_val.
      iModIntro. iNext.
      iIntros "Hz1". iMod ("Hclose" with "[Hz1 Hz2]"); eauto.
    - (* CAS *)
      smart_wp_bind (CasLCtx _ _) v1 "#Hv1" IHtyped1; cbn.
      smart_wp_bind (CasMCtx _ _) v2 "#Hv2" IHtyped2; cbn.
      smart_wp_bind (CasRCtx _ _) v3 "#Hv3" IHtyped3; cbn. iClear "HΓ".
      iDestruct "Hv1" as (l) "[% Hv1]"; subst.
      iApply wp_atomic.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      destruct (decide (v2 = w)) as [|Hneq]; subst.
      + iApply (wp_cas_suc with "Hw1"); auto using to_of_val.
        iModIntro. iNext.
        iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      + iApply (wp_cas_fail with "Hw1"); auto using to_of_val.
        iModIntro. iNext.
        iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    - iApply wp_wand_r; iSplitL; [iApply IHtyped|]; eauto.
      iIntros (?).
      iApply (logrel_subtyp with "[]"); eauto.
  Qed.
End typed_interp.
