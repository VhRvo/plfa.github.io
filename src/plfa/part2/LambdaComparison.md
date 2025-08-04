```agda
data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term
```

```agda
data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x N}
      ------------------------------
    → μ x ⇒ N —→ N [ x := μ x ⇒ N ]
```

```agda
data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ N ⦂ A
```

```agda
pushSubstType :
    {Γ : Context} {V N : Term} {A B C : Type} {x y : Id}
  → ∅ ⊢ V ⦂ A
  → Γ , y ⦂ A , x ⦂ B ⊢ N ⦂ C
  → Set
pushSubstType {Γ} {V} {N} {A} {B} {C} {x} {y} ⊢V ⊢N
  with x ≟ y
...  | yes _  =  Γ , x ⦂ B ⊢ N ⦂ C
...  | no  _  =  Γ , x ⦂ B ⊢ N [ y := V ] ⦂ C

pushSubst :
    {Γ : Context} {x y : Id} {V N : Term} {A B C : Type}
  → (⊢V : ∅ ⊢ V ⦂ A)
  → (⊢N : Γ , y ⦂ A , x ⦂ B ⊢ N ⦂ C)
  → pushSubstType ⊢V ⊢N

subst′ : ∀ {Γ y N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , y ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ y := V ] ⦂ B

pushSubst {Γ} {x} {y} ⊢V ⊢N
  with x ≟ y
...  | yes refl  =  drop ⊢N
...  | no  x≢y   =  subst ⊢V (swap x≢y ⊢N)
```
