From F_mu_ref_conc_sub Require Export context_refinement.
From iris.algebra Require Import auth frac agree.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From F_mu_ref_conc_sub Require Import soundness_unary.

Lemma basic_soundness Σ `{heapPreIG Σ, inG Σ (authR cfgUR)}
    e e' τ v thp hp :
  (∀ `{heapIG Σ, cfgSG Σ}, [] ∣ [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc erased_step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate NotStuck e ∅ (λ _ _, ∃ thp' h v, rtc erased_step ([e'], ∅) (of_val v :: thp', h))).
  { destruct 1; naive_solver. }
  eapply (wp_adequacy Σ _); iIntros (Hinv ?).
  iMod (gen_heap_init (∅ : gmap loc val)) as (GHG) "Hh".
  iMod (own_alloc (● (to_tpool [e'], ∅)
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_both_valid. split=>//. split=>//. apply to_tpool_valid. }
  set (Hcfg := CFGSG _ _ γc).
  iMod (inv_alloc specN _ (spec_inv ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists [e'], ∅. rewrite /to_gen_heap fin_maps.map_fmap_empty. auto. }
  set (HeapΣ := (HeapIG Σ Hinv GHG)).
  iExists (λ σ _, gen_heap_ctx σ); iFrame.
  iExists (λ _, True)%I.
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  iPoseProof ((Hlog _ _ [] [] ([e'], ∅)) with "[$Hcfg] [] []") as "Hrel".
  { iSplit; eauto. by iIntros (? ?); rewrite lookup_nil; iIntros (?). }
  { iApply (@logrel_binary.interp_env_nil Σ HeapΣ). }
  simpl.
  replace e with e.[env_subst[]] at 2 by by asimpl.
  iApply ("Hrel" $! 0 []).
  { rewrite /tpool_mapsto. asimpl. by iFrame. }
  iModIntro. iIntros (v1); iDestruct 1 as (v2) "[Hj #Hinterp]".
  iInv specN as (tp σ) ">[Hown Hsteps]" "Hclose"; iDestruct "Hsteps" as %Hsteps'.
  rewrite /tpool_mapsto /=.
  iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
  move: Hvalid=> /auth_both_valid
    [/prod_included [/tpool_singleton_included Hv2 _] _].
  destruct tp as [|? tp']; simplify_eq/=.
  iMod ("Hclose" with "[-]") as "_"; [iExists (_ :: tp'), σ; auto|].
  iIntros "!> !%"; eauto.
Qed.

Lemma binary_soundness Σ `{heapPreIG Σ, inG Σ (authR cfgUR)}
    Ξ Γ e e' τ :
  (Ξ |ₜ Γ ⊢ₜ e : τ) → (Ξ |ₜ Γ ⊢ₜ e' : τ) →
  (∀ `{heapIG Σ, cfgSG Σ}, Ξ ∣ Γ ⊨ e ≤log≤ e' : τ) →
  Ξ ∣ Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros He He' Hlog; repeat split; auto.
  intros K thp σ v ?. eapply (basic_soundness Σ _)=> ??.
  eapply (bin_log_related_under_typed_ctx); eauto.
Qed.
