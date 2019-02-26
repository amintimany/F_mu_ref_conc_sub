From F_mu_ref_conc_sub Require Export lang fundamental_binary.

Export F_mu_ref_conc.

Inductive ctx_item :=
  | CTX_Rec
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Nat bin op *)
  | CTX_BinOpL (op : binop) (e2 : expr)
  | CTX_BinOpR (op : binop) (e1 : expr)
  (* If *)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  (* Recursive Types *)
  | CTX_Fold
  | CTX_Unfold
  (* Polymorphic Types *)
  | CTX_TLam
  | CTX_TApp
  (* Concurrency *)
  | CTX_Fork
  (* Reference Types *)
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr)
  (* Compare and swap used for fine-grained concurrency *)
  | CTX_CAS_L (e1 : expr) (e2 : expr)
  | CTX_CAS_M (e0 : expr) (e2 : expr)
  | CTX_CAS_R (e0 : expr) (e1 : expr).

Fixpoint fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Rec => Rec e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_Fold => Fold e
  | CTX_Unfold => Unfold e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_Fork => Fork e
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  | CTX_CAS_L e1 e2 => CAS e e1 e2
  | CTX_CAS_M e0 e2 => CAS e0 e e2
  | CTX_CAS_R e0 e1 => CAS e0 e1 e
  end.

Definition ctx := list ctx_item.

Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** typed ctx *)
Inductive typed_ctx_item :
    ctx_item → list type → list type → type → list type → list type → type → Prop :=
  | TP_CTX_Rec Ξ Γ τ τ' :
     typed_ctx_item CTX_Rec Ξ (TArrow τ τ' :: τ :: Γ) τ' Ξ Γ (TArrow τ τ')
  | TP_CTX_AppL Ξ Γ e2 τ τ' :
     typed Ξ Γ e2 τ →
     typed_ctx_item (CTX_AppL e2) Ξ Γ (TArrow τ τ') Ξ Γ τ'
  | TP_CTX_AppR Ξ Γ e1 τ τ' :
     typed Ξ Γ e1 (TArrow τ τ') →
     typed_ctx_item (CTX_AppR e1) Ξ Γ τ Ξ Γ τ'
  | TP_CTX_PairL Ξ Γ e2 τ τ' :
     typed Ξ Γ e2 τ' →
     typed_ctx_item (CTX_PairL e2) Ξ Γ τ Ξ Γ (TProd τ τ')
  | TP_CTX_PairR Ξ Γ e1 τ τ' :
     typed Ξ Γ e1 τ →
     typed_ctx_item (CTX_PairR e1) Ξ Γ τ' Ξ Γ (TProd τ τ')
  | TP_CTX_Fst Ξ Γ τ τ' :
     typed_ctx_item CTX_Fst Ξ Γ (TProd τ τ') Ξ Γ τ
  | TP_CTX_Snd Ξ Γ τ τ' :
     typed_ctx_item CTX_Snd Ξ Γ (TProd τ τ') Ξ Γ τ'
  | TP_CTX_InjL Ξ Γ τ τ' :
     typed_ctx_item CTX_InjL Ξ Γ τ Ξ Γ (TSum τ τ')
  | TP_CTX_InjR Ξ Γ τ τ' :
     typed_ctx_item CTX_InjR Ξ Γ τ' Ξ Γ (TSum τ τ')
  | TP_CTX_CaseL Ξ Γ e1 e2 τ1 τ2 τ' :
     typed Ξ (τ1 :: Γ) e1 τ' → typed Ξ (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseL e1 e2) Ξ Γ (TSum τ1 τ2) Ξ Γ τ'
  | TP_CTX_CaseM Ξ Γ e0 e2 τ1 τ2 τ' :
     typed Ξ Γ e0 (TSum τ1 τ2) → typed Ξ (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseM e0 e2) Ξ (τ1 :: Γ) τ' Ξ Γ τ'
  | TP_CTX_CaseR Ξ Γ e0 e1 τ1 τ2 τ' :
     typed Ξ Γ e0 (TSum τ1 τ2) → typed Ξ  (τ1 :: Γ) e1 τ' →
     typed_ctx_item (CTX_CaseR e0 e1) Ξ (τ2 :: Γ) τ' Ξ Γ τ'
  | TP_CTX_IfL Ξ Γ e1 e2 τ :
     typed Ξ Γ e1 τ → typed Ξ Γ e2 τ →
     typed_ctx_item (CTX_IfL e1 e2) Ξ Γ (TBool) Ξ Γ τ
  | TP_CTX_IfM Ξ Γ e0 e2 τ :
     typed Ξ Γ e0 (TBool) → typed Ξ Γ e2 τ →
     typed_ctx_item (CTX_IfM e0 e2) Ξ Γ τ Ξ Γ τ
  | TP_CTX_IfR Ξ Γ e0 e1 τ :
     typed Ξ Γ e0 (TBool) → typed Ξ Γ e1 τ →
     typed_ctx_item (CTX_IfR e0 e1) Ξ Γ τ Ξ Γ τ
  | TP_CTX_BinOpL op Ξ Γ e2 :
     typed Ξ Γ e2 TNat →
     typed_ctx_item (CTX_BinOpL op e2) Ξ Γ TNat Ξ Γ (binop_res_type op)
  | TP_CTX_BinOpR op e1 Ξ Γ :
     typed Ξ Γ e1 TNat →
     typed_ctx_item (CTX_BinOpR op e1) Ξ Γ TNat Ξ Γ (binop_res_type op)
  | TP_CTX_Fold Ξ Γ τ :
     typed_ctx_item CTX_Fold Ξ Γ τ.[(TRec τ)/] Ξ Γ (TRec τ)
  | TP_CTX_Unfold Ξ Γ τ :
     typed_ctx_item CTX_Unfold Ξ Γ (TRec τ) Ξ Γ τ.[(TRec τ)/]
  | TP_CTX_TLam Ξ Γ σ τ :
     typed_ctx_item CTX_TLam (σ.[ren (+1)] :: (subst (ren (+1)) <$> Ξ))
                    (subst (ren (+1)) <$> Γ) τ Ξ Γ (TForall σ τ)
  | TP_CTX_TApp Ξ Γ σ τ τ' :
      subtype Ξ τ' σ →
     typed_ctx_item CTX_TApp Ξ Γ (TForall σ τ) Ξ Γ τ.[τ'/]
  | TP_CTX_Fork Ξ Γ :
     typed_ctx_item CTX_Fork Ξ Γ TUnit Ξ Γ TUnit
  | TPCTX_Alloc Ξ Γ τ :
     typed_ctx_item CTX_Alloc Ξ Γ τ Ξ Γ (Tref τ)
  | TP_CTX_Load Ξ Γ τ :
     typed_ctx_item CTX_Load Ξ Γ (Tref τ) Ξ Γ τ
  | TP_CTX_StoreL Ξ Γ e2 τ :
     typed Ξ Γ e2 τ → typed_ctx_item (CTX_StoreL e2) Ξ Γ (Tref τ) Ξ Γ TUnit
  | TP_CTX_StoreR Ξ Γ e1 τ :
     typed Ξ Γ e1 (Tref τ) →
     typed_ctx_item (CTX_StoreR e1) Ξ Γ τ Ξ Γ TUnit
  | TP_CTX_CasL Ξ Γ e1  e2 τ :
     EqType τ → typed Ξ Γ e1 τ → typed Ξ Γ e2 τ →
     typed_ctx_item (CTX_CAS_L e1 e2) Ξ Γ (Tref τ) Ξ Γ TBool
  | TP_CTX_CasM Ξ Γ e0 e2 τ :
     EqType τ → typed Ξ Γ e0 (Tref τ) → typed Ξ Γ e2 τ →
     typed_ctx_item (CTX_CAS_M e0 e2) Ξ Γ τ  Ξ Γ TBool
  | TP_CTX_CasR Ξ Γ e0 e1 τ :
     EqType τ → typed Ξ Γ e0 (Tref τ) → typed Ξ Γ e1 τ →
     typed_ctx_item (CTX_CAS_R e0 e1) Ξ Γ τ Ξ Γ TBool.

Lemma typed_ctx_item_typed k Ξ Γ τ Ξ' Γ' τ' e :
  typed Ξ Γ e τ → typed_ctx_item k Ξ Γ τ Ξ' Γ' τ' →
  typed Ξ' Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

Inductive typed_ctx :
  ctx → list type → list type → type → list type → list type → type → Prop :=
  | TPCTX_nil Ξ Γ τ :
     typed_ctx nil Ξ Γ τ Ξ Γ τ
  | TPCTX_cons Ξ1 Γ1 τ1 Ξ2 Γ2 τ2 Ξ3 Γ3 τ3 k K :
     typed_ctx_item k Ξ2 Γ2 τ2 Ξ3 Γ3 τ3 →
     typed_ctx K Ξ1 Γ1 τ1 Ξ2 Γ2 τ2 →
     typed_ctx (k :: K) Ξ1 Γ1 τ1 Ξ3 Γ3 τ3.

Lemma typed_ctx_typed K Ξ Γ τ Ξ' Γ' τ' e :
  typed Ξ Γ e τ → typed_ctx K Ξ Γ τ Ξ' Γ' τ' → typed Ξ' Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

(* Lemma typed_ctx_n_closed K Ξ Γ τ Ξ' Γ' τ' e : *)
(*   (∀ f, e.[upn (length Γ) f] = e) → typed_ctx K Ξ Γ τ Ξ' Γ' τ' → *)
(*   ∀ f, (fill_ctx K e).[upn (length Γ') f] = (fill_ctx K e). *)
(* Proof. *)
(*   intros H1 H2; induction H2; simpl; auto. *)
(*   induction H => f; asimpl; simpl in *; *)
(*     repeat match goal with H : _ |- _ => rewrite fmap_length in H end; *)
(*     try f_equal; *)
(*     eauto using typed_n_closed; *)
(*     try match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end. *)
(* Qed. *)

Definition ctx_refines (Ξ Γ : list type)
    (e e' : expr) (τ : type) :=
  typed Ξ Γ e τ ∧ typed Ξ Γ e' τ ∧
  ∀ K thp σ v,
  typed_ctx K Ξ Γ τ [] [] TUnit →
  rtc erased_step ([fill_ctx K e], ∅) (of_val v :: thp, σ) →
  ∃ thp' σ' v', rtc erased_step ([fill_ctx K e'], ∅) (of_val v' :: thp', σ').
Notation "Ξ ∣ Γ ⊨ e '≤ctx≤' e' : τ" :=
  (ctx_refines Ξ Γ e e' τ) (at level 74, e, e', τ at next level).

Section bin_log_related_under_typed_ctx.
  Context `{heapIG Σ, cfgSG Σ}.

  Lemma bin_log_related_under_typed_ctx Ξ Γ e e' τ Ξ' Γ' τ' K :
    typed_ctx K Ξ Γ τ Ξ' Γ' τ' →
    Ξ ∣ Γ ⊨ e ≤log≤ e' : τ → Ξ' ∣ Γ' ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ'.
  Proof.
    revert Ξ Γ τ Ξ' Γ' τ' e e'.
    induction K as [|k K]=> Ξ Γ τ Ξ' Γ' τ' e e' H1 H2; simpl.
    - inversion H1; subst; trivial.
    - inversion H1 as [|? ? ? ? ? ? ? ? ? ? ? Hx1 Hx2]; simplify_eq.
      specialize (IHK _ _ _ _ _ _ e e' Hx2 H2).
      inversion Hx1; subst; simpl.
      + eapply bin_log_related_rec; eauto.
      + eapply bin_log_related_app; eauto using binary_fundamental.
      + eapply bin_log_related_app; eauto using binary_fundamental.
      + eapply bin_log_related_pair; eauto using binary_fundamental.
      + eapply bin_log_related_pair; eauto using binary_fundamental.
      + eapply bin_log_related_fst; eauto.
      + eapply bin_log_related_snd; eauto.
      + eapply bin_log_related_injl; eauto.
      + eapply bin_log_related_injr; eauto.
      + eapply bin_log_related_case; eauto using binary_fundamental.
      + eapply bin_log_related_case; eauto using binary_fundamental.
      + eapply bin_log_related_case; eauto using binary_fundamental.
      + eapply bin_log_related_if; eauto using typed_ctx_typed, binary_fundamental.
      + eapply bin_log_related_if; eauto using typed_ctx_typed, binary_fundamental.
      + eapply bin_log_related_if; eauto using typed_ctx_typed, binary_fundamental.
      + eapply bin_log_related_nat_binop;
          eauto using typed_ctx_typed, binary_fundamental.
      + eapply bin_log_related_nat_binop;
          eauto using typed_ctx_typed, binary_fundamental.
      + eapply bin_log_related_fold; eauto.
      + eapply bin_log_related_unfold; eauto.
      + eapply bin_log_related_tlam; eauto with typeclass_instances.
      + eapply bin_log_related_tapp; eauto.
      + eapply bin_log_related_fork; eauto.
      + eapply bin_log_related_alloc; eauto.
      + eapply bin_log_related_load; eauto.
      + eapply bin_log_related_store; eauto using binary_fundamental.
      + eapply bin_log_related_store; eauto using binary_fundamental.
      + eapply bin_log_related_CAS; eauto using binary_fundamental.
      + eapply bin_log_related_CAS; eauto using binary_fundamental.
      + eapply bin_log_related_CAS; eauto using binary_fundamental.
  Qed.
End bin_log_related_under_typed_ctx.
