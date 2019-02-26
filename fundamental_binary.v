From iris.algebra Require Import list.
From F_mu_ref_conc_sub Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From F_mu_ref_conc_sub Require Import rules_binary.
From iris.program_logic Require Export lifting.

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (prodC valC valC -n> iProp Σ).

  Definition bin_log_related (Ξ Γ : list type) (e e' : expr) (τ : type) := ∀ Δ vvs ρ,
    env_Persistent Δ →
    spec_ctx ρ -∗ interp_Tenv Δ Ξ -∗
    ⟦ Γ ⟧* Δ vvs -∗ ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]).
End bin_log_def.

Notation "Ξ ∣ Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Ξ Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (prodC valC valC -n> iProp Σ).
  Implicit Types e : expr.
  Implicit Types Δ : listC D.
  Hint Resolve to_of_val.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]");
      [iApply Hp; iFrame "#"; trivial|];
    iIntros (v); iDestruct 1 as (w) Hv; simpl.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Ξ Γ e e' τ} : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ → ∀ Δ vvs ρ j K,
    env_Persistent Δ →
    interp_Tenv Δ Ξ ∗ spec_ctx ρ ∗ ⟦ Γ ⟧* Δ vvs ∗ j ⤇ fill K (e'.[env_subst (vvs.*2)])
    ⊢ WP e.[env_subst (vvs.*1)] {{ v, ∃ v',
        j ⤇ fill K (of_val v') ∗ interp τ Δ (v, v') }}.
  Proof.
    iIntros (Hlog Δ vvs ρ j K ?) "(#HΞ & #Hs & #HΓ & Hj)".
    iApply (Hlog with "[HΓ]"); iFrame; eauto.
  Qed.

  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_var Ξ Γ x τ :
    Γ !! x = Some τ → Ξ ∣ Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (? Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq ?]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_unit Ξ Γ : Ξ ∣ Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists UnitV; eauto.
  Qed.

  Lemma bin_log_related_nat Ξ Γ n : Ξ ∣ Γ ⊨ #n n ≤log≤ #n n : TNat.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#nv _); eauto.
  Qed.

  Lemma bin_log_related_bool Ξ Γ b : Ξ ∣ Γ ⊨ #♭ b ≤log≤ #♭ b : TBool.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#♭v _); eauto.
  Qed.

  Lemma bin_log_related_pair Ξ Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Ξ ∣ Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (PairLCtx e2.[env_subst _]) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((PairLCtx e2'.[env_subst _]) :: K)).
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ _ j ((PairRCtx v') :: K)).
    iApply wp_value. iExists (PairV v' w'); iFrame "Hw".
    iExists (v, v'), (w, w'); simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Ξ Γ e e' τ1 τ2
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Ξ ∣ Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ j (FstCtx :: K)); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_fst with "[Hs Hv]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_snd Ξ Γ e e' τ1 τ2
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Ξ ∣ Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ j (SndCtx :: K)); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_snd with "[Hs Hv]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_injl Ξ Γ e e' τ1 τ2
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ1) :
    Ξ ∣ Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ _ j (InjLCtx :: K)); cbn.
    iApply wp_value. iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Ξ Γ e e' τ1 τ2
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ2) :
    Ξ ∣ Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ _ j (InjRCtx :: K)); cbn.
    iApply wp_value. iExists (InjRV v'); iFrame "Hv".
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Ξ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3
      (IHHtyped1 : Ξ ∣ Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2)
      (IHHtyped2 : Ξ ∣ τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3)
      (IHHtyped3 : Ξ ∣ τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3) :
    Ξ ∣ Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((CaseCtx _ _) :: K)); cbn.
    iDestruct "Hiv" as "[Hiv|Hiv]";
    iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
    - iApply fupd_wp.
      iMod (step_case_inl with "[Hs Hv]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iModIntro. iNext.
      asimpl.
      iApply ('`IHHtyped2 _ ((w,w') :: vvs)); iFrame; iFrame "#".
      iApply interp_env_cons; auto.
    - iApply fupd_wp.
      iMod (step_case_inr with "[Hs Hv]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iModIntro. iNext.
      asimpl.
      iApply ('`IHHtyped3 _ ((w,w') :: vvs)); iFrame; iFrame "#".
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_if Ξ Γ e0 e1 e2 e0' e1' e2' τ
      (IHHtyped1 : Ξ ∣ Γ ⊨ e0 ≤log≤ e0' : TBool)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : τ)
      (IHHtyped3 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ) :
    Ξ ∣ Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (IfCtx _ _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((IfCtx _ _) :: K)); cbn.
    iDestruct "Hiv" as ([]) "[% %]"; simplify_eq/=; iApply fupd_wp.
    - iMod (step_if_true _ _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. iModIntro. iNext.
      iApply '`IHHtyped2; eauto.
    - iMod (step_if_false _ _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto.
      iModIntro. iNext. iApply '`IHHtyped3; eauto.
  Qed.

  Lemma bin_log_related_nat_binop Ξ Γ op e1 e2 e1' e2'
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : TNat)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : TNat) :
    Ξ ∣ Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (BinOpLCtx _ _) v v' "[Hv #Hiv]"
                  ('`IHHtyped1 _ _ _ j ((BinOpLCtx _ _) :: K)); cbn.
    smart_wp_bind (BinOpRCtx _ _) w w' "[Hw #Hiw]"
                  ('`IHHtyped2 _ _ _ j ((BinOpRCtx _ _) :: K)); cbn.
    iDestruct "Hiv" as (n) "[% %]"; simplify_eq/=.
    iDestruct "Hiw" as (n') "[% %]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_nat_binop _ _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro. iNext.
    iApply wp_value. iExists _; iSplitL; eauto.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; eauto.
  Qed.

  Lemma bin_log_related_rec Ξ Γ (e e' : expr) τ1 τ2
      (IHHtyped : Ξ ∣ TArrow τ1 τ2 :: τ1 :: Γ ⊨ e ≤log≤ e' : τ2) :
    Ξ ∣ Γ ⊨ Rec e ≤log≤ Rec e' : TArrow τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (RecV _). iIntros "{$Hj} !#".
    iLöb as "IH". iIntros ([v v']) "#Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iApply fupd_wp.
    iMod (step_rec _ _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. change (Rec ?e) with (of_val (RecV e)).
    iApply ('`IHHtyped _ ((_,_) :: (v,v') :: vvs)); iFrame; iFrame "#".
    iModIntro.
    rewrite !interp_env_cons; repeat iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_lam Ξ Γ (e e' : expr) τ1 τ2
      (IHHtyped : Ξ ∣ τ1 :: Γ ⊨ e ≤log≤ e' : τ2) :
    Ξ ∣ Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (LamV _). iIntros "{$Hj} !#".
    iIntros ([v v']) "#Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iApply fupd_wp.
    iMod (step_lam _ _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. iFrame "#". change (Lam ?e) with (of_val (LamV e)).
    iApply ('`IHHtyped _  ((v,v') :: vvs)); repeat iSplit; eauto.
    iModIntro.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_letin Ξ Γ (e1 e2 e1' e2' : expr) τ1 τ2
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Ξ ∣ τ1 :: Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Ξ ∣ Γ ⊨ LetIn e1 e2 ≤log≤ LetIn e1' e2': τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (LetInCtx _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((LetInCtx _) :: K)); cbn.
    iMod (step_letin _ _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    asimpl.
    iApply ('`IHHtyped2 _ ((v, v') :: vvs)); iFrame; iFrame "#".
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_seq Ξ Γ (e1 e2 e1' e2' : expr) τ1 τ2
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Ξ ∣ Γ ⊨ Seq e1 e2 ≤log≤ Seq e1' e2': τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (SeqCtx _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((SeqCtx _) :: K)); cbn.
    iMod (step_seq _ _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    asimpl.
    iApply '`IHHtyped2; iFrame; iFrame "#".
  Qed.

  Lemma bin_log_related_app Ξ Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ1) :
    Ξ ∣ Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (AppLCtx (e2.[env_subst (vvs.*1)])) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j (((AppLCtx (e2'.[env_subst (vvs.*2)]))) :: K)); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                  ('`IHHtyped2 _ _ _ j ((AppRCtx v') :: K)); cbn.
    iApply ("Hiv" $! (w, w') with "Hiw"); simpl; eauto.
  Qed.

  Lemma bin_log_related_tlam Ξ Γ e e' σ τ
      (IHHtyped : σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ) ∣ subst (ren (+1)) <$> Γ ⊨ e ≤log≤ e' : τ) :
    Ξ ∣ Γ ⊨ TLam e ≤log≤ TLam e' : TForall σ τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (TLamV _).
    iIntros "{$Hj} /= !#"; iIntros (τi ?).
    iIntros "#Hsb". iIntros (j' K') "Hv /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply fupd_wp.
    iMod (step_tlam _ _ j' K' (e'.[env_subst (vvs.*2)]) with "[-]") as "Hz";
      eauto.
    iApply '`IHHtyped; repeat iSplit; eauto.
    iModIntro; iFrame "#"; iFrame. rewrite interp_env_ren; iFrame "#".
    rewrite -interp_Tenv_weaken; iFrame "#".
  Qed.

  Lemma bin_log_related_tapp Ξ Γ e e' σ τ τ'
        (Hsb : subtype Ξ τ' σ)
        (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : TForall σ τ) :
    Ξ ∣ Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (TAppCtx) v v' "[Hj #Hv]"
      ('`IHHtyped _ _ _ j (TAppCtx :: K)) ; simpl.
    rewrite -/interp.
    iApply wp_wand_r; iSplitL.
    { iSpecialize ("Hv" $! (interp τ' Δ) with "[#]"); [iPureIntro; apply _|].
      iApply "Hv"; eauto.
      iAlways. iIntros (?). iApply (logrel_subtyp with "[]"); eauto. }
    iIntros (w). iDestruct 1 as (w') "[Hw Hiw]".
    iExists _; rewrite -interp_subst; eauto.
  Qed.

  Lemma bin_log_related_fold Ξ Γ e e' τ
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) :
    Ξ ∣ Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply (wp_bind (fill [FoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply ('`IHHtyped _ _ _ j (FoldCtx :: K)); iFrame; iFrame "#"].
    iIntros (v); iDestruct 1 as (w) "[Hv #Hiv]".
    iApply wp_value. iExists (FoldV w); iFrame "Hv".
    rewrite fixpoint_interp_rec1_eq /= -interp_subst.
    iAlways; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Ξ Γ e e' τ
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : TRec τ) :
    Ξ ∣ Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply (wp_bind (fill [UnfoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply ('`IHHtyped _ _ _ j (UnfoldCtx :: K));
          iFrame; iFrame "#"].
    iIntros (v). iDestruct 1 as (v') "[Hw #Hiw]".
    rewrite /= fixpoint_interp_rec1_eq /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hiw" as ([w w']) "#[% Hiz]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_Fold _ _ j K (of_val w') w' with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto.
    iModIntro. iApply wp_value. iNext; iExists _; iFrame "Hz".
      by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fork Ξ Γ e e'
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : TUnit) :
    Ξ ∣ Γ ⊨ Fork e ≤log≤ Fork e' : TUnit.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply fupd_wp.
    iMod (step_fork _ _ j K with "[-]") as (j') "[Hj Hj']"; eauto.
    iApply wp_fork; iModIntro. rewrite -bi.later_sep. iNext; iSplitL "Hj".
    - iExists UnitV; eauto.
    - iApply wp_wand_l; iSplitR; [|iApply ('`IHHtyped _ _ _ _ [])]; eauto.
  Qed.

  Lemma bin_log_related_alloc Ξ Γ e e' τ
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ) :
    Ξ ∣ Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ j (AllocCtx :: K)).
    iApply fupd_wp.
    iMod (step_alloc _ _ j K (of_val v') v' with "[-]") as (l') "[Hj Hl]"; eauto.
    iApply wp_atomic; eauto.
    iApply wp_alloc; eauto. do 2 iModIntro. iNext.
    iIntros (l) "Hl'".
    iMod (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ᵢ w.1 ∗ l' ↦ₛ w.2 ∗ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { iNext. iExists (v, v'); iFrame. iFrame "Hiv". }
    iModIntro; iExists (LocV l'). iFrame "Hj". iExists (l, l'); eauto.
  Qed.

  Lemma bin_log_related_load Ξ Γ e e' τ
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : (Tref τ)) :
    Ξ ∣ Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ j (LoadCtx :: K)).
    iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([w w']) "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    (* TODO: why can we eliminate the next modality here? ↑ *)
    iModIntro.
    iApply (wp_load with "Hw1").
    iNext. iIntros "Hw1".
    iMod (step_load  with "[Hv Hw2]") as "[Hv Hw2]";
      [solve_ndisj|by iFrame|].
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists (w,w'); by iFrame. }
    iModIntro. iExists w'; by iFrame.
  Qed.

  Lemma bin_log_related_store Ξ Γ e1 e2 e1' e2' τ
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : (Tref τ))
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ) :
    Ξ ∣ Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((StoreLCtx _) :: K)).
    smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ _ j ((StoreRCtx _) :: K)).
    iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([v v']) "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    iApply (wp_store with "Hv1"); auto using to_of_val.
    iNext. iIntros "Hw2".
    iMod (step_store with "[Hs Hw Hv2]") as "[Hw Hv2]"; eauto;
    [solve_ndisj | by iFrame|].
    iMod ("Hclose" with "[Hw2 Hv2]").
    { iNext; iExists (w, w'); simpl; iFrame. iFrame "Hiw". }
    iExists UnitV; iFrame; auto.
  Qed.

  Lemma bin_log_related_CAS Ξ Γ e1 e2 e3 e1' e2' e3' τ
      (HEqτ : EqType τ)
      (IHHtyped1 : Ξ ∣ Γ ⊨ e1 ≤log≤ e1' : Tref τ)
      (IHHtyped2 : Ξ ∣ Γ ⊨ e2 ≤log≤ e2' : τ)
      (IHHtyped3 : Ξ ∣ Γ ⊨ e3 ≤log≤ e3' : τ) :
    Ξ ∣  Γ ⊨ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' : TBool.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    smart_wp_bind (CasLCtx _ _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ j ((CasLCtx _ _) :: K)).
    smart_wp_bind (CasMCtx _ _) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ _  j ((CasMCtx _ _) :: K)).
    smart_wp_bind (CasRCtx _ _) u u' "[Hu #Hiu]"
      ('`IHHtyped3 _ _ _  j ((CasRCtx _ _) :: K)).
    iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iMod (interp_ref_open' _ _ l l' with "[]") as
        (v v') "(>Hl & >Hl' & #Hiv & Heq & Hcl)"; eauto.
    { iExists (_, _); eauto. }
    iModIntro.
    destruct (decide (v = w)) as [|Hneq]; subst.
    - iApply (wp_cas_suc with "Hl"); eauto using to_of_val; eauto.
      iNext. iIntros "Hl".
      iMod ("Heq" with "Hl Hl' Hiv Hiw") as "(Hl & Hl' & Heq)".
      iDestruct "Heq" as %[-> _]; last trivial.
      iMod (step_cas_suc
            with "[Hu Hl']") as "[Hw Hl']"; simpl; eauto; first solve_ndisj.
      { iFrame. iFrame "#". }
      iMod ("Hcl" with "[Hl Hl']").
      { iNext; iExists (_, _); by iFrame. }
      iExists (#♭v true); iFrame; eauto.
    - iApply (wp_cas_fail with "Hl"); eauto using to_of_val; eauto.
      iNext. iIntros "Hl".
      iMod ("Heq" with "Hl Hl' Hiv Hiw") as "(Hl & Hl' & Heq)".
      iDestruct "Heq" as %[_ Heq].
      assert (v' ≠ w').
      { by intros ?; apply Hneq; rewrite Heq. }
      iMod (step_cas_fail
            with "[$Hs Hu Hl']") as "[Hw Hl']"; simpl; eauto; first solve_ndisj.
      iFrame.
      iMod ("Hcl" with "[Hl Hl']").
      { iNext; iExists (_, _); by iFrame. }
      iExists (#♭v false); eauto.
  Qed.

  Lemma bin_log_related_subtype Ξ Γ e e' τ τ'
        (Hsb : subtype Ξ τ τ')
      (IHHtyped : Ξ ∣ Γ ⊨ e ≤log≤ e' : τ) :
    Ξ ∣ Γ ⊨ e ≤log≤ e' : τ'.
  Proof.
    iIntros (Δ vvs ρ ?) "#Hs #HΞ #HΓ"; iIntros (j K) "Hj /=".
    iApply wp_wand_r; iSplitL.
    { iApply IHHtyped; iFrame "#"; iFrame. }
    iIntros (?); iDestruct 1 as (?) "[? #?]"; iExists _; iFrame.
    iApply logrel_subtyp; eauto.
  Qed.

  Theorem binary_fundamental Ξ Γ e τ :
    Ξ |ₜ Γ ⊢ₜ e : τ → Ξ ∣ Γ ⊨ e ≤log≤ e : τ.
  Proof.
    induction 1.
    - by apply bin_log_related_var.
    - by apply bin_log_related_unit.
    - by apply bin_log_related_nat.
    - by apply bin_log_related_bool.
    - apply bin_log_related_nat_binop; eauto.
    - apply bin_log_related_pair; eauto.
    - eapply bin_log_related_fst; eauto.
    - eapply bin_log_related_snd; eauto.
    - eapply bin_log_related_injl; eauto.
    - eapply bin_log_related_injr; eauto.
    - eapply bin_log_related_case; eauto.
    - eapply bin_log_related_if; eauto.
    - eapply bin_log_related_rec; eauto.
    - eapply bin_log_related_lam; eauto.
    - eapply bin_log_related_letin; eauto.
    - eapply bin_log_related_seq; eauto.
    - eapply bin_log_related_app; eauto.
    - eapply bin_log_related_tlam; eauto.
    - eapply bin_log_related_tapp; eauto.
    - eapply bin_log_related_fold; eauto.
    - eapply bin_log_related_unfold; eauto.
    - eapply bin_log_related_fork; eauto.
    - eapply bin_log_related_alloc; eauto.
    - eapply bin_log_related_load; eauto.
    - eapply bin_log_related_store; eauto.
    - eapply bin_log_related_CAS; eauto.
    - eapply bin_log_related_subtype; eauto.
  Qed.

End fundamental.
