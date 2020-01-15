Require Import WildCat.Core.

(* Squares of morphisms in a Wild Category *)

Section Squares.
  Context {A : Type} `{Is1Cat A} {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  Definition Square {x00 x20 x02 x22} (f10 : x00 $-> x20) (f12 : x02 $-> x22) (f01 : x00 $-> x02) (f21 : x20 $-> x22) : Type :=
    f21 $o f10 $== f12 $o f01.

  Definition Build_Square (p : f21 $o f10 $== f12 $o f01) : Square f10 f12 f01 f21 := p.
  Definition gpdhom_square (p : Square f10 f12 f01 f21) : f21 $o f10 $== f12 $o f01 := p.

  Definition hdeg_square {f f' : x $-> x'} (p : f $== f') : Square (Id x) (Id x') f f' := 
    cat_idr f' $@ p^$ $@ (cat_idl f)^$.
  Definition vdeg_square {f f' : x $-> x'} (p : f $== f') : Square f f' (Id x) (Id x') := 
    cat_idl f $@ p $@ (cat_idr f')^$.

  Definition hrefl (f : x $-> x') : Square (Id x) (Id x') f f := hdeg_square (Id f).
  Definition vrefl (f : x $-> x') : Square f f (Id x) (Id x') := vdeg_square (Id f).
  Definition hrfl {f : x $-> x'} : Square (Id x) (Id x') f f := hrefl f.
  Definition vrfl {f : x $-> x'} : Square f f (Id x) (Id x') := vrefl f.


End Squares.



(*
section psquare
  /-
    Squares of pointed maps
    We treat expressions of the form
      psquare f g h k :≡ k ∘* f ~* g ∘* h
    as squares, where f is the top, g is the bottom, h is the left face and k is the right face.
    These squares are very useful for naturality squares
  -/

  variables {A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₁₄ : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ : A₄₀ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}

  definition hsquare_of_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare f₁₀ f₁₂ f₀₁ f₂₁ :=
  to_homotopy p

  variables (f₁₀ f₁₂ f₀₁ f₂₁)
  definition phconst_square : psquare !pconst !pconst f₀₁ f₂₁ :=
  !pcompose_pconst ⬝* !pconst_pcompose⁻¹*
  definition pvconst_square : psquare f₁₀ f₁₂ !pconst !pconst :=
  !pconst_pcompose ⬝* !pcompose_pconst⁻¹*

  definition ptranspose (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare f₀₁ f₂₁ f₁₀ f₁₂ :=
  p⁻¹*

  definition phconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₃₀ f₃₂ f₂₁ f₄₁) :
    psquare (f₃₀ ∘* f₁₀) (f₃₂ ∘* f₁₂) f₀₁ f₄₁ :=
  !passoc⁻¹* ⬝* pwhisker_right f₁₀ q ⬝* !passoc ⬝* pwhisker_left f₃₂ p ⬝* !passoc⁻¹*

  definition pvconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    psquare f₁₀ f₁₄ (f₀₃ ∘* f₀₁) (f₂₃ ∘* f₂₁) :=
  !passoc ⬝* pwhisker_left _ p ⬝* !passoc⁻¹* ⬝* pwhisker_right _ q ⬝* !passoc

  definition phinverse {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀⁻¹ᵉ* f₁₂⁻¹ᵉ* f₂₁ f₀₁ :=
  !pid_pcompose⁻¹* ⬝* pwhisker_right _ (pleft_inv f₁₂)⁻¹* ⬝* !passoc ⬝*
  pwhisker_left _
    (!passoc⁻¹* ⬝* pwhisker_right _ p⁻¹* ⬝* !passoc ⬝* pwhisker_left _ !pright_inv ⬝* !pcompose_pid)

  definition pvinverse {f₀₁ : A₀₀ ≃* A₀₂} {f₂₁ : A₂₀ ≃* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₂ f₁₀ f₀₁⁻¹ᵉ* f₂₁⁻¹ᵉ* :=
  (phinverse p⁻¹*)⁻¹*

  definition phomotopy_hconcat (q : f₀₁' ~* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀ f₁₂ f₀₁' f₂₁ :=
  p ⬝* pwhisker_left f₁₂ q⁻¹*

  definition hconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₂₁' ~* f₂₁) :
    psquare f₁₀ f₁₂ f₀₁ f₂₁' :=
  pwhisker_right f₁₀ q ⬝* p

  definition phomotopy_vconcat (q : f₁₀' ~* f₁₀) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀' f₁₂ f₀₁ f₂₁ :=
  pwhisker_left f₂₁ q ⬝* p

  definition vconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₁₂' ~* f₁₂) :
    psquare f₁₀ f₁₂' f₀₁ f₂₁ :=
  p ⬝* pwhisker_right f₀₁ q⁻¹*

  infix ` ⬝h* `:73 := phconcat
  infix ` ⬝v* `:73 := pvconcat
  infixl ` ⬝hp* `:72 := hconcat_phomotopy
  infixr ` ⬝ph* `:72 := phomotopy_hconcat
  infixl ` ⬝vp* `:72 := vconcat_phomotopy
  infixr ` ⬝pv* `:72 := phomotopy_vconcat
  postfix `⁻¹ʰ*`:(max+1) := phinverse
  postfix `⁻¹ᵛ*`:(max+1) := pvinverse

  definition pwhisker_tl (f : A →* A₀₀) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (f₁₀ ∘* f) f₁₂ (f₀₁ ∘* f) f₂₁ :=
  !passoc⁻¹* ⬝* pwhisker_right f q ⬝* !passoc

  definition ap1_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω→ f₁₀) (Ω→ f₁₂) (Ω→ f₀₁) (Ω→ f₂₁) :=
  !ap1_pcompose⁻¹* ⬝* ap1_phomotopy p ⬝* !ap1_pcompose

  definition apn_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω→[n] f₁₀) (Ω→[n] f₁₂) (Ω→[n] f₀₁) (Ω→[n] f₂₁) :=
  !apn_pcompose⁻¹* ⬝* apn_phomotopy n p ⬝* !apn_pcompose

  end psquare

  definition pinverse_natural [constructor] {X Y : Type*} (f : X →* Y) :
    psquare (pinverse X) (pinverse Y) (Ω→ f) (Ω→ f) :=
  phomotopy.mk (ap1_gen_inv f (respect_pt f) (respect_pt f))
    abstract begin
      induction Y with Y y₀, induction f with f f₀, esimp at * ⊢, induction f₀, reflexivity
    end end

  definition pcast_natural [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : psquare (pcast (ap B p)) (pcast (ap C p)) (f a₁) (f a₂) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, exact whisker_left idp !ap_id end

  definition pequiv_of_eq_natural [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) :
    psquare (pequiv_of_eq (ap B p)) (pequiv_of_eq (ap C p)) (f a₁) (f a₂) :=
  pcast_natural f p

  definition loopn_succ_in_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    psquare (loopn_succ_in n A) (loopn_succ_in n B) (Ω→[n+1] f) (Ω→[n] (Ω→ f)) :=
  begin
    induction n with n IH,
    { exact phomotopy.rfl },
    { exact ap1_psquare IH }
  end

  definition loopn_succ_in_inv_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    psquare (loopn_succ_in n A)⁻¹ᵉ* (loopn_succ_in n B)⁻¹ᵉ* (Ω→[n] (Ω→ f)) (Ω→[n + 1] f) :=
  (loopn_succ_in_natural n f)⁻¹ʰ*

  definition pnatural_square {A B : Type} (X : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* X (g a)) {a a' : A} (p : a = a') :
   psquare (ptransport X (ap f p)) (ptransport X (ap g p)) (h a) (h a') :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*
  *)