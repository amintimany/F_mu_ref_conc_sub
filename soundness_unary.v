From F_mu_ref_conc_sub Require Export fundamental_unary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import auth.

Class heapPreIG Σ := HeapPreIG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc F_mu_ref_conc.val Σ
}.

Theorem soundness Σ `{heapPreIG Σ} e τ e' thp σ σ' :
  (∀ `{heapIG Σ}, [] | [] ⊨ e : τ) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ _). iIntros (Hinv ?).
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply (auth_auth_valid _ (to_gen_heap_valid _ _ σ)). }
  iModIntro. iExists (λ σ _, own γ (● to_gen_heap σ)); iFrame.
  set (HeapΣ := (HeapIG Σ Hinv (GenHeapG _ _ Σ _ _ _ γ))).
  iApply (wp_wand with "[]").
  - replace e with e.[env_subst[]] by by asimpl.
    iApply (Hlog HeapΣ [] []).
    { iSplit; eauto. by iIntros (? ?); rewrite lookup_nil; iIntros (?). }
    iApply (@interp_env_nil _ HeapΣ).
  - eauto.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] |ₜ [] ⊢ₜ e : τ →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := #[invΣ ; gen_heapΣ loc F_mu_ref_conc.val]).
  set (HG := HeapPreIG Σ _ _).
  eapply (soundness Σ); eauto using fundamental.
Qed.
