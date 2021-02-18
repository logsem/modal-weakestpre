From mwp Require Export mwp.
From iris.proofmode Require Import tactics.

Definition ictr {Λ Σ} (mwpd: mwpData Λ Σ) `{!mwpC mwpd} idx (E : coPset) (P : iProp Σ)
    (e : expr Λ) (Φ : val Λ → nat → mwpC_Extra → iProp Σ) : iProp Σ :=
  (□ (P -∗ MWP@{mwpd, idx} e @ E {{ Φ }}))%I.
Instance: Params (@ictr) 7 := {}.

Notation "{{| P '|}}@{' R , idx } e @ E {{| Φ '|}}'" := (ictr R idx E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{|  Φ  '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n , Q '|}}'" :=
  (ictr R idx E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v , Φ '|}}'" :=
  (ictr R idx E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v , Φ '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R idx E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v | [ x ] , Q '|}}'" :=
  (ictr R idx E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R idx E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R idx E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.


Notation "{{| P '|}}@{' R , idx } e {{| Φ '|}}'" := (ictr R idx ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  idx }  e  {{|  Φ  '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n , Q '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v , Φ '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v , Φ '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v | [ x ] , Q '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R idx ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.



Notation "{{| P '|}}@{' R , idx } e @ E {{| Φ '|}}'" :=
  (True ⊢ ictr R idx E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{|  Φ  '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v , Φ '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v , Φ '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R idx E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.


Notation "{{| P '|}}@{' R , idx } e {{| Φ '|}}'" := (True ⊢ ictr R idx ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  idx }  e  {{|  Φ  '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v , Φ '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v , Φ '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , idx } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R idx ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  idx }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.



Notation "{{| P '|}}@{' R } e @ E {{| Φ '|}}'" := (ictr R tt E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R }  e  @  E  {{|  Φ  '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n , Q '|}}'" :=
  (ictr R tt E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v , Φ '|}}'" :=
  (ictr R tt E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v , Φ '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R tt E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v | [ x ] , Q '|}}'" :=
  (ictr R tt E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R tt E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R tt E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.


Notation "{{| P '|}}@{' R } e {{| Φ '|}}'" := (ictr R tt ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R }  e  {{|  Φ  '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n , Q '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v , Φ '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v , Φ '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v | [ x ] , Q '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R tt ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.




Notation "{{| P '|}}@{' R } e @ E {{| Φ '|}}'" :=
  (True ⊢ ictr R tt E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R }  e  @  E  {{|  Φ  '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v , Φ '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v , Φ '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R tt E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.


Notation "{{| P '|}}@{' R } e {{| Φ '|}}'" := (True ⊢ ictr R tt ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R }  e  {{|  Φ  '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v , Φ '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v , Φ '|}}'") : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R tt ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.





Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{|  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v , Φ '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v | [ x ] , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. )
        E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. )
        E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.


Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{|  Φ  '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v , Φ '|}}'") : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n | [ x ] , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v | [ x ] , Q '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v | [ x ] ,  Q  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. )
        ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (ictr R (pair idx .. (pair idy idz) .. )
        ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : bi_scope.



Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) E P e%E Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{|  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v , Φ '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) E P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. )
     E P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e @ E {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. )
     E P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  @  E  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.


Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E Φ)
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{|  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v n _, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v _ _, Φ))
  (at level 20, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v , Φ '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v n x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v | [ x ] , Q '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. ) ⊤ P e%E (λ v _ x, Q))
  (at level 20, P, e, Q at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v | [ x ] ,  Q  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v ; n | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. )
     ⊤ P e%E (λ v n r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v ;  n | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Notation "{{| P '|}}@{' R , [ idx .. idy idz ] } e {{| v | x ; .. ; y , Φ '|}}'" :=
  (True ⊢ ictr R (pair idx .. (pair idy idz) .. )
     ⊤ P e%E (λ v _ r, @from_Prod_fun (@mwpC_Extra _ _ R _) _ ( λ x , .. (λ y , Φ) ..) r))
  (at level 20, x closed binder, y closed binder, P, e, Φ at level 200,
  format "{{|  P  '|}}@{' R ,  [ idx .. idy idz ] }  e  {{| v | x ; .. ; y ,  Φ  '|}}'")
  : stdpp_scope.

Section hoare.
Context {Λ Σ} (mwpd: mwpData Λ Σ) `{!mwpC mwpd}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val Λ → nat → mwpC_Extra → iProp Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ictr_ne idx E n :
  Proper (dist n ==> eq ==>
               (pointwise_relation
                  _ (pointwise_relation
                       _ (pointwise_relation _ (dist n)))) ==> dist n)
         (ictr mwpd idx E).
Proof. unfold ictr. solve_proper. Qed.
Global Instance ictr_proper idx E :
  Proper ((≡) ==> eq ==>
               (pointwise_relation
                  _ (pointwise_relation
                       _ (pointwise_relation _ (≡)))) ==> (≡))
         (ictr mwpd idx E).
Proof. unfold ictr. solve_proper. Qed.

Lemma ictr_mono idx E P P' Φ Φ' e :
  (P ⊢ P') → (∀ v n x, Φ' v n x ⊢ Φ v n x) →
  {{| P' |}}@{mwpd, idx} e @ E {{| Φ' |}} ⊢ {{| P |}}@{mwpd, idx} e @ E {{| Φ |}}.
Proof.
  iIntros (HPr HPs) "#H !# HP".
  iApply mwp_mono; eauto.
  by iApply "H"; iApply HPr.
Qed.

Global Instance ictr_mono' idx E :
  Proper (flip (⊢) ==> eq ==>
               (pointwise_relation
                  _ (pointwise_relation
                       _ (pointwise_relation _ (⊢)))) ==> (⊢))
         (ictr mwpd idx E).
Proof. unfold ictr. solve_proper. Qed.

Lemma ictr_alt idx E P Φ e :
  (P ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}) → {{| P |}}@{mwpd, idx} e @ E {{| Φ |}}.
Proof. iIntros (Hic) "_ !# HP". by iApply Hic. Qed.

Lemma ictr_val idx E v ξ :
  {{| mwpC_modality mwpd idx E 0 ξ |}}@{mwpd, idx}
    of_val v @ E {{| v' ; n | [x], ⌜v = v' ∧ n = 0⌝ ∗ ξ x |}}.
Proof.
  iIntros "_ !# ?". iApply mwp_value'.
  iApply mwpC_modality_mono; last done; eauto.
Qed.

Lemma ictr_bind `{LanguageCtx Λ K} idx idx' f g E P Φ Φ' e :
  mwpC_modality_bind_condition mwpd idx idx' f g →
  {{| P |}}@{mwpd, idx'} e @ E {{| Φ |}} ∧
  (∀ v n x, {{| Φ v n x |}}@{mwpd, f x}
              K (of_val v) @ E {{| w; m | [y], Φ' w (n + m) (g x y) |}})
    ⊢ {{| P |}}@{mwpd, idx} K e @ E {{| Φ' |}}.
Proof.
  iIntros (Hidx) "[#Hice #HicK] !# HP". iApply mwp_bind; eauto.
  iApply mwp_wand_r; iSplitL; first by iApply "Hice".
  iIntros (v n x) "Hv". by iApply "HicK".
Qed.

Lemma ictr_mask_weaken idx E1 E2 P Φ e :
  E1 ⊆ E2 → {{| P |}}@{mwpd, idx} e @ E1 {{| Φ |}} ⊢ {{| P |}}@{mwpd, idx} e @ E2 {{| Φ |}}.
Proof.
  iIntros (?) "#Hic !# HP". iApply (mwp_mask_mono _ _ E1 E2); try done.
  by iApply "Hic".
Qed.

Lemma ictr_frame_l idx E P Φ R e :
  {{| P |}}@{mwpd, idx} e @ E {{| Φ |}}
  ⊢ {{| R ∗ P |}}@{mwpd, idx} e @ E {{| v; n | [x], R ∗ Φ v n x |}}.
Proof. iIntros "#Hic !# [$ HP]". by iApply "Hic". Qed.

Lemma ictr_frame_r idx E P Φ R e :
  {{| P |}}@{mwpd, idx} e @ E {{| Φ |}}
  ⊢ {{| P ∗ R |}}@{mwpd, idx} e @ E {{| v; n | [x], Φ v n x ∗ R |}}.
Proof. iIntros "#Hic !# [HP $]". by iApply "Hic". Qed.

End hoare.
