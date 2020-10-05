From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From iris.proofmode Require Import base tactics classes.
From mwp Require Export reduction base.
Import uPred.

Inductive Prod :=
| PrNil : Prod
| PrCons : Type → Prod → Prod.

Notation "'[Prod' ]" := PrNil (format "[Prod ]") : type_scope.
Notation "'[Prod' x ]" := (PrCons x PrNil) (format "[Prod  x ]") : type_scope.
Notation "'[Prod' x ; y ; .. ; z ]" :=
  (PrCons x (PrCons y .. (PrCons z PrNil) ..))
    (format "[Prod  x ;  y ;  .. ;  z ]") : type_scope.

Fixpoint TypeOfProd (a : Prod) : Type :=
match a with
| PrNil => unit
| PrCons A b =>
  match b with
  | PrNil => A
  | _ => A * TypeOfProd b
  end
end.

Global Coercion TypeOfProd : Prod >-> Sortclass.

Fixpoint Prod_fun (a : Prod) (B : Type) : Type :=
match a with
| PrNil => B
| PrCons A b =>
  match b with
  | PrNil => A → B
  | _ => A → (Prod_fun b B)
  end
end.

Fixpoint to_Prod_fun {a : Prod} {B : Type} (f : a → B) {struct a} :
  Prod_fun a B :=
match a as u return (u → B) → Prod_fun u B with
| PrNil => λ g, g tt
| PrCons A b =>
  match b as v return
        ((v → B) → Prod_fun v B) →
        (PrCons A v → B) → Prod_fun (PrCons A v) B with
  | PrNil => λ F g x, g x
  | PrCons C p => λ F g x, F (λ y, g (x, y))
  end (@to_Prod_fun b B)
end f.

Fixpoint from_Prod_fun {a : Prod} {B : Type} (f : Prod_fun a B) : a → B :=
match a as u return Prod_fun u B → u → B with
| PrNil => λ y _, y
| PrCons A b =>
  match b as v return
        (Prod_fun v B → v → B) →
        (Prod_fun (PrCons A v) B) → (PrCons A v) → B with
  | PrNil => λ F g x, g x
  | PrCons C p => λ F g x, F (g (fst x)) (snd x)
  end (@from_Prod_fun b B)
end f.

Record mwpData (Λ : language) (Σ : gFunctors) := Build_mwpData {
  mwpD_Extra : Prod;
  mwpD_state_interp : state Λ → iProp Σ;
  mwpD_modality_index : Prod;
  mwpD_modality_bind_condition :
    mwpD_modality_index →
    mwpD_modality_index →
    (mwpD_Extra → mwpD_modality_index) →
    (mwpD_Extra → mwpD_Extra → mwpD_Extra) → Prop;
  mwpD_modality :
    mwpD_modality_index → coPset → nat → (mwpD_Extra → iProp Σ) → iProp Σ;
}.

Class mwpC {Λ Σ} (mwpD : mwpData Λ Σ) := Build_IRG {
  mwpC_Extra : Prod := mwpD_Extra _ _ mwpD;
  mwpC_state_interp : state Λ → iProp Σ := mwpD_state_interp _ _ mwpD;
  mwpC_modality_index : Prod := mwpD_modality_index _ _ mwpD;
  mwpC_modality :
    mwpC_modality_index → coPset → nat → (mwpC_Extra → iProp Σ) → iProp Σ :=
    mwpD_modality _ _ mwpD;
  mwpC_modality_ne :>
    ∀ idx E m n, Proper (pointwise_relation _ (dist m) ==> (dist m))
                      (λ f, mwpC_modality idx E n f);
  mwpC_modality_mono :
    ∀ idx E1 E2 n Φ Ψ,
      E1 ⊆ E2 → (∀ x, Φ x -∗ Ψ x)
        ⊢ mwpC_modality idx E1 n Φ -∗ mwpC_modality idx E2 n Ψ;
  (* The modality must be a monad *)
  mwpC_modality_intro :
    ∀ idx E n Φ, mwpC_modality idx E 0 Φ ⊢ mwpC_modality idx E n Φ;
  mwpC_modality_bind_condition :
    mwpC_modality_index →
    mwpC_modality_index →
    (mwpC_Extra → mwpC_modality_index) →
    (mwpC_Extra → mwpC_Extra → mwpC_Extra) → Prop :=
    mwpD_modality_bind_condition _ _ mwpD;
  mwpC_modality_bind : ∀ idx idx' f g E n m Φ,
      mwpC_modality_bind_condition idx idx' f g →
      mwpC_modality idx' E n (λ x, mwpC_modality (f x) E m (λ z, Φ (g x z)))
      ⊢ mwpC_modality idx E (n + m) Φ;
}.

Global Arguments mwpC_state_interp {_ _} _ {_} _ : simpl never.
Global Arguments mwpC_modality {_ _} _ {_} _ _ _ : simpl never.
Global Arguments mwpC_modality_bind_condition {_ _} _ {_} : simpl never.

Class mwpMIsOuterModal {Λ Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx
      (M : coPset → nat → iProp Σ → iProp Σ) :=
  mwp_modality_is_outer_modal :
    ∀ E n P, M E n (mwpC_modality mwpd idx E n P) ⊢ (mwpC_modality mwpd idx E n P).

Class mwpMIsInnerModal {Λ Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx
      (M : coPset → nat → iProp Σ → iProp Σ) :=
  mwp_modality_is_inner_modal :
    ∀ E n P, (mwpC_modality mwpd idx E n (λ x, M E n (P x)))
               ⊢ (mwpC_modality mwpd idx E n P).

Class mwpMAlwaysSupportsShift
      {Λ Σ} `{!invG Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx :=
  mwp_always_supports_shift : ∀ n E1 E2 P,
    (|={E1, E2}=> mwpC_modality mwpd idx E2 n (λ x, |={E2, E1}=> P x))
      ⊢ (mwpC_modality mwpd idx E1 n P).

Class mwpMSupportsAtomicShift
      {Λ Σ} `{!invG Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx :=
  mwp_supports_atomic_shift : ∀ n E1 E2 P, n ≤ 1 →
    (|={E1, E2}=> mwpC_modality mwpd idx E2 n (λ x, |={E2, E1}=> P x))
      ⊢ (mwpC_modality mwpd idx E1 n P).

Global Instance mwpMAlwaysSupportsAtomicShift
       {Λ Σ} `{!invG Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx :
  mwpMAlwaysSupportsShift mwpd idx → mwpMSupportsAtomicShift mwpd idx.
Proof. rewrite /mwpMAlwaysSupportsShift /mwpMSupportsAtomicShift; auto. Qed.

Class mwpMSplitForStep {Λ Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx :=
{
  mwpM_split_for_step_M1 : coPset → iProp Σ → iProp Σ;
  mwpM_split_for_step_M2 : coPset → iProp Σ → iProp Σ;
  mwpM_split_for_step_split n E P :
    mwpM_split_for_step_M1 E
     (mwpM_split_for_step_M2 E
      (mwpC_modality mwpd idx E n P))  ⊢ mwpC_modality mwpd idx E (S n) P;
  mwpM_split_for_step_M1_mono E P Q :
    (P -∗ Q) ⊢ mwpM_split_for_step_M1 E P -∗ mwpM_split_for_step_M1 E Q;
  mwpM_split_for_step_M2_mono E P Q :
    (P -∗ Q) ⊢ mwpM_split_for_step_M2 E P -∗ mwpM_split_for_step_M2 E Q;
}.

Class mwpCMElimCond n m := mwpC_modality_elim_cond : n ≤ m.

Global Hint Extern 10 (mwpCMElimCond _ _) =>
  unfold mwpCMElimCond; (lia || eassumption): typeclass_instances.

Typeclasses Opaque mwpC_state_interp mwpC_modality.

Global Instance mwpC_modality_from_modal {Λ Σ} (mwpd : mwpData Λ Σ)
       `{!mwpC mwpd} idx (Φ : mwpC_Extra → iProp Σ) E n :
  FromModal modality_id (True : Prop) (mwpC_modality mwpd idx E n Φ)
            (mwpC_modality mwpd idx E 0 Φ).
Proof.
  rewrite /FromModal. iIntros "HP"; simpl.
  by iApply mwpC_modality_intro.
Qed.

Global Instance mwpC_modality_mono'  {Λ Σ} (mwpd : mwpData Λ Σ)
       `{!mwpC mwpd} idx E n :
  Proper (pointwise_relation _ bi_entails ==> bi_entails) (λ f, mwpC_modality mwpd idx E n f).
Proof.
  iIntros (P Q HPQ). iApply mwpC_modality_mono; first done.
  iIntros (x); iApply HPQ.
Qed.

Global Instance mwpC_modality_elim_fupd {Λ Σ} (mwpd : mwpData Λ Σ)
       `{!mwpC mwpd} idx `{!invG Σ} `{!mwpMIsOuterModal mwpd idx (λ E n P, |={E}=> P)%I}
       (P : iProp Σ) (Φ : mwpC_Extra → iProp Σ) p E E' n :
  ElimModal True p false (|={E, E'}=> P) P
            (mwpC_modality mwpd idx E n Φ) (|={E', E}=> mwpC_modality mwpd idx E n Φ).
Proof.
  rewrite /ElimModal /=.
  iIntros (?) "[HP HPQ]"; rewrite intuitionistically_if_elim.
  iApply mwp_modality_is_outer_modal. iMod "HP".
  by iMod ("HPQ" with "HP").
Qed.

Global Instance mwpC_modality_elim_is_bupd {Λ Σ} (mwpd : mwpData Λ Σ)
       `{!mwpC mwpd} idx `{!mwpMIsOuterModal mwpd idx (λ E n P, |==> P)%I}
       (P : iProp Σ) (Φ : mwpC_Extra → iProp Σ) p E n :
  ElimModal True p false (|==> P) P
            (mwpC_modality mwpd idx E n Φ) (|==> mwpC_modality mwpd idx E n Φ).
Proof.
  rewrite /ElimModal /=.
  iIntros (?) "[HP HPQ]"; rewrite intuitionistically_if_elim.
  iApply mwp_modality_is_outer_modal. iMod "HP".
  by iMod ("HPQ" with "HP").
Qed.

Class ExecutesPurely {Λ} (e : expr Λ) := executes_purely :
    ∀ σ1 σ2 v n, relations.nsteps pstep n (e, σ1) (of_val v, σ2) → σ1 = σ2.

Class PureLang Λ := pure_language :
    ∀ (e1 : expr Λ) σ1 σ2 e2, pstep (e1, σ1) (e2, σ2) → σ1 = σ2.

Global Instance PureLang_ExecutesPurely `{! PureLang Λ} (e : expr Λ) :
  ExecutesPurely e.
Proof.
  intros σ1 σ2 v n; revert e σ1 σ2 v.
  induction n; intros e σ1 σ2 v Hr.
  { by inversion Hr; simplify_eq. }
  inversion Hr as [|? ? [e' σ'] ? Hps]; simpl in *; simplify_eq.
  apply pure_language in Hps; subst.
  eauto.
Qed.

Definition mwp_def {Λ Σ} (mwpd: mwpData Λ Σ) `{!mwpC mwpd}
           idx E e (Φ : val Λ → nat → mwpC_Extra → iProp Σ) : iProp Σ :=
  (∀ σ1 σ2 v n,
      ⌜relations.nsteps pstep n (e, σ1) (of_val v, σ2)⌝ -∗
       mwpC_state_interp mwpd σ1 -∗
       mwpC_modality mwpd idx E n (λ x, Φ v n x ∗ mwpC_state_interp mwpd σ2))%I.
Definition mwp_aux : seal (@mwp_def). Proof. by eexists. Qed.
Definition mwp {Λ Σ} RM idx {H} E e Φ := mwp_aux.(unseal) Λ Σ RM idx H E e Φ.
Definition mwp_eq : @mwp = @mwp_def := mwp_aux.(seal_eq).

Arguments mwp {_ _} _ {_} _ _ _%E _.
Instance: Params (@mwp) 8 := {}.

Notation "'MWP@{' R , idx } e @ E {{ Φ } }" := (mwp R idx E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v ; n , Q } }" :=
  (mwp R idx E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v , Φ } }" :=
  (mwp R idx E e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v ; n | [ x ] , Q } }" :=
  (mwp R idx E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v ; n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R idx E e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x, .. (λ y, Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v | [ x ] , Q } }" :=
  (mwp R idx E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (mwp R idx E e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'MWP@{' R , idx } e {{ Φ } }" := (mwp R idx ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v ; n , Q } }" :=
  (mwp R idx ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v , Φ } }" :=
  (mwp R idx ⊤ e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v ; n | [ x ] , Q } }" :=
  (mwp R idx ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R idx ⊤ e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v | [ x ] , Q } }" :=
  (mwp R idx ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , idx } e {{ v | x ; .. ; y , Φ } }" :=
  (mwp R idx ⊤ e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  idx }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'MWP@{' R } e @ E {{ Φ } }" :=
  (mwp R tt E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ Φ } }" := (mwp R tt E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v ; n , Q } }" :=
  (mwp R tt E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v , Φ } }" :=
  (mwp R tt E e%E (λ v _ _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v ; n | [ x ] , Q } }" :=
  (mwp R tt E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  @  E  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R tt E e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v | [ x ] , Q } }" :=
  (mwp R tt E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  @  E  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (mwp R tt E e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'MWP@{' R } e {{ Φ } }" :=
  (mwp R tt ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R }  e  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v ; n , Q } }" :=
  (mwp R tt ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v , Φ } }" :=
  (mwp R tt ⊤ e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v ; n | [ x ] , Q } }" :=
  (mwp R tt ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  {{ v ;  n  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R tt ⊤ e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v | [ x ] , Q } }" :=
  (mwp R tt ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R }  e  {{ v  |  [ x ] ,  Q  } }") : bi_scope.

Notation "'MWP@{' R } e {{ v | x ; .. ; y , Φ } }" :=
  (mwp R tt ⊤ e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }") : bi_scope.


Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R , [ idx .. idy idz ] }  e  @  E  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v ; n , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) E e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) E e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v ; n | [ x ] , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) E e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. )
      E e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v | [ x ] , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) E e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e @ E {{ v | x ; .. ; y , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. )
      E e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  @  E  {{ v  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.


Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R , [ idx .. idy idz ] }  e  {{  Φ  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v ; n , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n _, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n ,  Q  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n _, Φ))
  (at level 20, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v ,  Φ  } }") : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v ; n | [ x ] , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v n x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v ; n | x ; .. ; y , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. )
      ⊤ e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v ;  n  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v | [ x ] , Q } }" :=
  (mwp R (pair idx .. (pair idy idz) .. ) ⊤ e%E (λ v _ x, Q))
  (at level 20, e, Q at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v  |  [ x ] ,  Q  } }")
  : bi_scope.

Notation "'MWP@{' R , [ idx .. idy idz ] } e {{ v | x ; .. ; y , Φ } }" :=
  (mwp R (pair idx .. (pair idy idz) .. )
      ⊤ e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, e, Φ at level 200,
   format "'MWP@{' R ,  [ idx .. idy idz ] }  e  {{ v  |  x ;  .. ;  y ,  Φ  } }")
  : bi_scope.


(* Texan mwp triples *)
Notation "'{{{|' P '|}}}@{' R , idx } e @ E {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ MWP@{R, idx} e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R ,  idx }  e  @  E  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R } e @ E {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ MWP@{R} e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R }  e  @  E  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R , idx } e {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ MWP@{R, idx} e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R ,  idx }  e  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Notation "'{{{|' P '|}}}@{' R } e {{{| x ; .. ; y ; PATS , Q '|}}}'" :=
  (□ ∀ Φ,
      P ∗ ▷ (∀ x, .. (∀ y, Q -∗ PATS Φ) .. ) -∗ MWP@{R} e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{|  P  '|}}}@{' R }  e  {{{| x ;  .. ;  y ;  PATS ,  Q '|}}}'") : bi_scope.

Section mwp.
Context `(mwpd : mwpData Λ Σ) `{!mwpC mwpd}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → nat → mwpC_Extra → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

Global Instance mwp_ne idx E e n :
  Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n))) ==> dist n)
         (@mwp Λ Σ mwpd _ idx E e).
Proof.
  intros Φ1 Φ2 R; rewrite mwp_eq /mwp_def.
  do 10 f_equiv.
  apply mwpC_modality_ne; f_equiv.
  repeat f_equiv; apply R.
Qed.

Global Instance mwp_proper idx E e :
  Proper (pointwise_relation
            _ (pointwise_relation _ (pointwise_relation _ (≡))) ==> (≡))
         (@mwp Λ Σ mwpd _ idx E e).
Proof.
  intros Φ Φ' R.
  apply equiv_dist=>m; apply mwp_ne =>v k x. by rewrite R.
Qed.

Lemma mwp_intro idx E e `{!ExecutesPurely e} Φ :
  (∀ v n, mwpC_modality mwpd idx E n (Φ v n)) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  rewrite mwp_eq /mwp_def.
  iIntros "HΦ".
  iIntros (σ1 σ2 v n Hr) "Hsi".
  iSpecialize ("HΦ" $! v n).
  iApply (mwpC_modality_mono with "[Hsi]"); try done.
  iIntros (x) "?".
  rewrite (executes_purely _ _ _ _ Hr); iFrame.
Qed.

Lemma mwp_value' idx E Φ v :
  mwpC_modality mwpd idx E 0 (Φ v 0) -∗ MWP@{mwpd, idx} of_val v @ E {{ Φ }}.
Proof.
  rewrite mwp_eq /mwp_def.
  iIntros "H" (? ? ? ? [? [? ?]]%nsteps_val); simplify_eq.
  iIntros "Hi".
  iApply mwpC_modality_intro.
  iApply (mwpC_modality_mono with "[Hi] H"); simpl; auto.
  iIntros (?) "?"; iFrame.
Qed.

Lemma mwp_strong_mono_Mod
      M idx `{!mwpMIsInnerModal mwpd idx (λ E n P, M E P)%I}
      E1 E2 e Φ Ψ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  E1 ⊆ E2 → (∀ v n x, Φ v n x -∗ M E2 (Ψ v n x))
              ∗ MWP@{mwpd, idx} e @ E1 {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (HM Hsb) "[Hi H]". rewrite mwp_eq /mwp_def.
  iIntros (σ1 σ2 v n) "Hr Ho".
  iSpecialize ("H" $! σ1 σ2 v n with "Hr Ho").
  iApply mwp_modality_is_inner_modal.
  iApply (mwpC_modality_mono with "[Hi] H"); first done.
  iIntros (x) "[HΦ Hsi]".
  iSpecialize ("Hi" with "HΦ").
  iApply (HM with "[Hsi]"); last done.
  by iIntros "?"; iFrame.
Qed.

Lemma mwp_strong_mono_fupd
      `{!invG Σ} idx `{!mwpMIsInnerModal mwpd idx (λ E n P, |={E}=> P)%I} E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  (∀ v n x, Φ v n x ={E2}=∗ Ψ v n x) ∗ MWP@{mwpd, idx} e @ E1 {{ Φ }}
   ⊢ MWP@{mwpd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply mwp_strong_mono_Mod; eauto.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma mwp_strong_mono_bupd
      idx `{!mwpMIsInnerModal mwpd idx (λ E n P, |==> P)%I} E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v n x, Φ v n x ==∗ Ψ v n x)
              ∗ MWP@{mwpd, idx} e @ E1 {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply mwp_strong_mono_Mod; eauto.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma mwp_strong_mono_wand idx E1 E2 e Φ Ψ :
  E1 ⊆ E2 →
  (∀ v n x, Φ v n x -∗ Ψ v n x) ∗ MWP@{mwpd, idx} e @ E1 {{ Φ }}
  ⊢ MWP@{mwpd, idx} e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "?"; iApply (mwp_strong_mono_Mod (λ _ P, P)); eauto.
  rewrite /mwpMIsInnerModal; eauto.
Qed.

Lemma Mod_mwp M idx `{!mwpMIsOuterModal mwpd idx (λ E n P, M E P)%I} E e Φ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  (M E (MWP@{mwpd, idx} e @ E {{ Φ }})) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  rewrite mwp_eq /mwp_def.
  iIntros (HM) "Hm".
  iIntros (σ1 σ2 v n) "% Ho".
  iApply mwp_modality_is_outer_modal.
  iApply (HM with "[Ho]"); last done.
  iIntros "Hm". by iApply "Hm".
Qed.

Lemma mwp_Mod M idx `{!mwpMIsInnerModal mwpd idx (λ E n P, M E P)%I} E e Φ :
  (∀ E P Q, (P -∗ Q) ⊢ M E P -∗ M E Q) →
  MWP@{mwpd, idx} e @ E {{ v ; n | [x], M E (Φ v n x) }}
  ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros (HM) "H".
  iApply (mwp_strong_mono_Mod _ idx E); try iFrame; auto.
  by iIntros (? ? ?) "H ?"; iApply (HM with "H").
Qed.

Lemma fupd_mwp `{!invG Σ} idx
      `{!mwpMIsOuterModal mwpd idx (λ E n P, |={E}=> P)%I}
 E e Φ : (|={E}=> MWP@{mwpd, idx} e @ E {{ Φ }}) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_mwp (λ E P, |={E}=> P))%I.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma mwp_fupd
      `{!invG Σ} idx `{!mwpMIsInnerModal mwpd idx (λ E n P, |={E}=> P)%I} E e Φ :
  MWP@{mwpd, idx} e @ E {{ v; n | [x], |={E}=> Φ v n x }}
  ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (mwp_strong_mono_fupd _ E); try iFrame; auto.
Qed.

Lemma bupd_mwp idx
      `{!mwpMIsOuterModal mwpd idx (λ E n P, |==> P)%I}
 E e Φ : (|==> MWP@{mwpd, idx} e @ E {{ Φ }}) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_mwp (λ E P, |==> P))%I.
  by iIntros (? ? ?) "H >?"; iApply "H".
Qed.

Lemma mwp_bupd idx `{!mwpMIsInnerModal mwpd idx (λ E n P, |==> P)%I} E e Φ :
  MWP@{mwpd, idx} e @ E {{ v; n | [x], |==> Φ v n x }}
  ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (mwp_strong_mono_bupd _ E); try iFrame; auto.
 Qed.

Lemma except_0_mwp idx `{!mwpMIsOuterModal mwpd idx (λ E n P, ◇ P)%I}
 E e Φ : (◇ MWP@{mwpd, idx} e @ E {{ Φ }}) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iApply (Mod_mwp (λ E P, ◇ P))%I.
  by iIntros (? ? ?) "H >?"; iModIntro; iApply "H".
Qed.

Lemma mwp_except_0 idx `{!mwpMIsInnerModal mwpd idx (λ E n P, ◇ P)%I} E e Φ :
  MWP@{mwpd, idx} e @ E {{ v; n | [x], ◇ Φ v n x }}
  ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply (mwp_strong_mono_Mod (λ E P, ◇ P)%I); eauto; last iFrame; auto.
  by iIntros (???) "H >?"; iModIntro; iApply "H".
Qed.

Lemma mwp_bind K `{!LanguageCtx K} idx idx' f g E e Φ :
  mwpC_modality_bind_condition mwpd idx idx' f g →
  MWP@{mwpd, idx'} e @ E {{ v; m | [x],
      MWP@{mwpd, f x} K (of_val v) @ E
        {{ w; n | [y], Φ w (m + n) (g x y) }} }}
  ⊢ MWP@{mwpd, idx} K e @ E {{ Φ }}.
Proof.
  iIntros (Hcnd) "H".
  rewrite mwp_eq /mwp_def.
  iIntros (σ1 σ2 w n Hr) "Hsi".
  destruct (nsteps_bind _ Hr) as (k & σ' & u & Hle & Hstp1 & Hstp2).
  iSpecialize ("H" with "[] Hsi"); eauto.
  replace n with (k + (n - k)) by lia.
  iApply mwpC_modality_bind; eauto.
  iApply (mwpC_modality_mono); simpl; last done; first auto.
  iIntros (x) "[H Hsi]".
  iSpecialize ("H" with "[] Hsi"); by eauto.
Qed.

Lemma mwp_atomic `{!invG Σ} idx `{!mwpMSupportsAtomicShift mwpd idx}
      a E1 E2 e Φ `{!Atomic a e} :
  (|={E1,E2}=> MWP@{mwpd, idx} e @ E2 {{ v; n | [x], |={E2,E1}=> Φ v n x }})
  ⊢ MWP@{mwpd, idx} e @ E1 {{ Φ }}.
Proof.
  rewrite mwp_eq /mwp_def.
  iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
  pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
  iApply mwp_supports_atomic_shift; eauto.
  iMod "H"; iModIntro.
  iSpecialize ("H" with "[] Ho"); eauto.
  iApply mwpC_modality_mono; last done; auto.
  iIntros (?)  "[>H Hsi]".
  iModIntro; iFrame.
Qed.

Lemma mwp_shift `{!invG Σ} idx `{!mwpMAlwaysSupportsShift mwpd idx}
      E1 E2 e Φ :
  (|={E1,E2}=> MWP@{mwpd, idx} e @ E2 {{ v; n | [x], |={E2,E1}=> Φ v n x }})
  ⊢ MWP@{mwpd, idx} e @ E1 {{ Φ }}.
Proof.
  rewrite mwp_eq /mwp_def.
  iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
  iApply mwp_always_supports_shift; eauto.
  iMod "H"; iModIntro.
  iSpecialize ("H" with "[] Ho"); eauto.
  iApply mwpC_modality_mono; last done; auto.
  iIntros (?) "[>H Hsi]".
  iModIntro; iFrame.
Qed.

Lemma mwp_change_of_index idx idx' f E e Φ :
  (∀ Ψ n, mwpC_modality mwpd idx' E n (Ψ ∘ f) -∗ mwpC_modality mwpd idx E n Ψ)
    -∗ MWP@{mwpd, idx'} e @ E {{ λ v n x, Φ v n (f x)}}
  -∗ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros "Hm H".
  rewrite mwp_eq /mwp_def.
  iIntros (σ1 σ2 v n Hr) "Hsi".
  iApply ("Hm").
  by iApply "H".
Qed.

(** * Derived rules *)
Lemma mwp_mono idx E e Φ Ψ : (∀ v n x, Φ v n x ⊢ Ψ v n x) →
  MWP@{mwpd, idx} e @ E {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H". iApply mwp_strong_mono_wand; eauto.
  iFrame.
  by iIntros (v n x); iApply HΦ.
Qed.
Lemma mwp_mask_mono idx E1 E2 e Φ : E1 ⊆ E2 →
  MWP@{mwpd, idx} e @ E1 {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (mwp_strong_mono_wand); eauto; iFrame; eauto. Qed.
Global Instance mwp_mono' idx E e :
  Proper (pointwise_relation
            _ (pointwise_relation _ (pointwise_relation _ (⊢))) ==> (⊢))
         ( @mwp Λ Σ mwpd _ idx E e).
Proof. intros ???. by apply mwp_mono => ???; apply H. Qed.

Lemma mwp_value idx E Φ e v :
  IntoVal e v →
  mwpC_modality mwpd idx E 0 (Φ v 0) ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof. intros <-. by rewrite mwp_value'. Qed.

Lemma mwp_frame_l idx E e Φ R :
  R ∗ MWP@{mwpd, idx} e @ E {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E {{ v; n | [x], R ∗ Φ v n x }}.
Proof.
  iIntros "[??]".
  iApply (mwp_strong_mono_wand _ _ _ _ Φ); try iFrame; eauto.
Qed.
Lemma mwp_frame_r idx E e Φ R :
  MWP@{mwpd, idx} e @ E {{ Φ }} ∗ R ⊢ MWP@{mwpd, idx} e @ E {{ v; n | [x], Φ v n x ∗ R }}.
Proof.
  iIntros "[??]".
  iApply (mwp_strong_mono_wand _ _ _ _ Φ); try iFrame; eauto.
Qed.

Lemma mwp_wand_l idx E e Φ Ψ :
  (∀ v n x, Φ v n x -∗ Ψ v n x) ∗
  MWP@{mwpd, idx} e @ E {{ Φ }} ⊢ MWP@{mwpd, idx} e @ E {{ Ψ }}.
Proof.
  iIntros "[H Hmwp]". iApply (mwp_strong_mono_wand _ E); auto.
  iFrame "Hmwp". iIntros (???) "?". by iApply "H".
Qed.
Lemma mwp_wand_r idx E e Φ Ψ :
  MWP@{mwpd, idx} e @ E {{ Φ }} ∗
  (∀ v n x, Φ v n x -∗ Ψ v n x)
  ⊢ MWP@{mwpd, idx} e @ E {{ Ψ }}.
Proof. by rewrite comm mwp_wand_l. Qed.
End mwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {Λ Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → nat → mwpC_Extra → iProp Σ.

  Global Instance frame_mwp p idx E e R Φ Ψ :
    (∀ v n x, Frame p R (Φ v n x) (Ψ v n x)) →
    Frame p R (MWP@{mwpd, idx} e @ E {{ Φ }}) (MWP@{mwpd, idx} e @ E {{ Ψ }}).
  Proof.
    rewrite /Frame=> HR.
    rewrite mwp_frame_l.
    apply mwp_mono.
    apply HR.
  Qed.

  Global Instance is_except_0_mwp idx `{!mwpMIsOuterModal mwpd idx (λ E n P, ◇ P)%I}
         E e Φ : IsExcept0 (MWP@{mwpd, idx} e @ E {{ Φ }}).
  Proof.
    rewrite /IsExcept0 mwp_eq /mwp_def.
    iIntros "H".
    iIntros (σ1 σ2 v n Hrd) "Ho".
    iApply mwp_modality_is_outer_modal.
    iMod "H"; iModIntro.
    by iApply "H".
  Qed.

  Global Instance elim_modal_bupd_mwp idx
         `{!mwpMIsOuterModal mwpd idx (λ E n P, |==> P)%I} p E e P Φ :
    ElimModal True p false (|==> P) P (MWP@{mwpd, idx} e @ E {{ Φ }})
              (MWP@{mwpd, idx} e @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim /=.
    iIntros (_) "[H1 H2]".
    rewrite mwp_eq /mwp_def.
    iIntros (σ1 σ2 v n Hrd) "Ho".
    iApply mwp_modality_is_outer_modal.
    iMod "H1". iModIntro.
    by iApply ("H2" with "H1").
  Qed.

  Global Instance elim_modal_fupd_mwp
        `{invG Σ} `{!mwpMIsOuterModal mwpd idx (λ E n P, |={E}=> P)%I} p E e P Φ :
    ElimModal True p false (|={E}=> P) P (MWP@{mwpd, idx} e @ E {{ Φ }})
              (MWP@{mwpd, idx} e @ E {{ Φ }}).
  Proof.
      by rewrite /ElimModal intuitionistically_if_elim /=
                 fupd_frame_r wand_elim_r fupd_mwp.
  Qed.

End proofmode_classes.
