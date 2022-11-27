{-# OPTIONS --safe #-}
module Cubical.HITs.Pushout.IsPushout where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

-- TODO: Move these somewhere else

sym≡ : {A : Type ℓ} {a a' : A} → (a ≡ a') ≃ (a' ≡ a)
sym≡ {a = a} {a' = a'} = isoToEquiv i
  where
    open Iso
    i : Iso (a ≡ a') (a' ≡ a)
    i .fun p = sym p
    i .inv p = sym p
    i .rightInv p = refl
    i .leftInv p = refl

-- TODO: Move to separate file (Whiskering)

_◃_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : B → C) {g g' : A → B} (α : g ≡ g') → f ∘ g ≡ f ∘ g'
f ◃ α = cong (f ∘_) α

_▹_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : B → C} (α : f ≡ f') (g : A → B) → f ∘ g ≡ f' ∘ g
α ▹ g = cong (_∘ g) α



module _ {A B C P : Type ℓ} (f : A → B) (g : A → C) (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g)
  where

  pushoutComparison : (E : Type ℓ) → (P → E) → Σ[ g'' ∈ (B → E) ] Σ[ f'' ∈ (C → E) ] g'' ∘ f ≡ f'' ∘ g
  pushoutComparison E h .fst = h ∘ g'
  pushoutComparison E h .snd .fst = h ∘ f'
  pushoutComparison E h .snd .snd = h ◃ α

  record isPushout : Type (ℓ-suc ℓ) where
    no-eta-equality
    field
      comparisonIsEquiv : (E : Type ℓ) → isEquiv (pushoutComparison E)

  open isPushout

  isPropIsPushout : isProp isPushout
  comparisonIsEquiv (isPropIsPushout po po' i) =
    isPropΠ (λ E → isPropIsEquiv _) (po .comparisonIsEquiv) (po' .comparisonIsEquiv) i

open isPushout

module _ {A B C : Type ℓ} (f : A → B) (g : A → C) where
  -- The HIT `Pushout f g` is a pushout

  PushoutIsPushout : isPushout {P = Pushout f g} f g inl inr (funExt push)
  comparisonIsEquiv PushoutIsPushout E = isoToIsEquiv i
    where
      open Iso
      i : Iso (Pushout f g → E) _
      i .fun = pushoutComparison f g inl inr (funExt push) E
      i .inv s (inl b) = s .fst b
      i .inv s (inr c) = s .snd .fst c
      i .inv s (push a k) = s .snd .snd k a
      i .rightInv s = refl
      i .leftInv h j (inl b) = h (inl b)
      i .leftInv h j (inr c) = h (inr c)
      i .leftInv h j (push a k) = h (push a k)

  -- Induced map out of the pushout

  SpanCoconeOn : Type ℓ → Type ℓ
  SpanCoconeOn D = Σ[ g' ∈ (B → D) ] Σ[ f' ∈ (C → D) ] g' ∘ f ≡ f' ∘ g

  module SpanCoconeOn {D : Type ℓ} (sco : SpanCoconeOn D) where
    g' : B → D
    g' = sco .fst

    f' : C → D
    f' = sco .snd .fst

    α' : g' ∘ f ≡ f' ∘ g
    α' = sco .snd .snd

  SpanCocone : Type (ℓ-suc ℓ)
  SpanCocone = Σ (Type ℓ) SpanCoconeOn

  module SpanCocone (sc : SpanCocone) where
    open SpanCoconeOn (sc .snd) public

    D : Type ℓ
    D = sc .fst

    SCIsPushout : Type (ℓ-suc ℓ)
    SCIsPushout = isPushout f g g' f' α'

  module _ {D₁ D₂ : Type ℓ} (sco₁ : SpanCoconeOn D₁) (sco₂ : SpanCoconeOn D₂) (h : D₁ → D₂) where
    open SpanCoconeOn sco₁ renaming (g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCoconeOn sco₂ renaming (g' to g₂ ; f' to f₂ ; α' to α₂)

    SpanCoconeHomOver : Type ℓ
    SpanCoconeHomOver =
      Σ[ pg ∈ g₂ ≡ h ∘ g₁ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] (pg ▹ f) ∙∙ (h ◃ α₁) ∙∙ (pf ▹ g) ≡ α₂

    ≡≃SCHO : ((h ∘ g₁ , h ∘ f₁ , h ◃ α₁) ≡ sco₂) ≃ SpanCoconeHomOver
    ≡≃SCHO =
        ((h ∘ g₁ , h ∘ f₁ , h ◃ α₁) ≡ sco₂)
      ≃⟨ compEquiv (invEquiv ΣPath≃PathΣ) (Σ-cong-equiv-snd (λ pg' → invEquiv ΣPath≃PathΣ)) ⟩
        Σ[ pg' ∈ h ∘ g₁ ≡ g₂ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] PathP (λ i → pg' i ∘ f ≡ pf i ∘ g) (h ◃ α₁) α₂
      ≃⟨ Σ-cong-equiv-fst sym≡ ⟩
        Σ[ pg ∈ g₂ ≡ h ∘ g₁ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] PathP (λ i → pg (~ i) ∘ f ≡ pf i ∘ g) (h ◃ α₁) α₂
      ≃⟨ Σ-cong-equiv-snd (λ pg → Σ-cong-equiv-snd (λ pf →
           pathToEquiv (PathP≡doubleCompPathˡ (cong (_∘ f) (sym pg)) (h ◃ α₁) α₂ (cong (_∘ g) pf)))) ⟩
        SpanCoconeHomOver
      ■

  module _ {sc₁ : SpanCocone} (po : SpanCocone.SCIsPushout sc₁) (sc₂ : SpanCocone) where
    open isPushout
    open SpanCocone sc₁ renaming (D to D₁ ; g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCocone sc₂ renaming (D to D₂ ; g' to g₂ ; f' to f₂ ; α' to α₂)

    private module _ where
      h : D₁ → D₂
      h = invIsEq (comparisonIsEquiv po D₂) (sc₂ .snd)

      h≡ : (h ∘ g₁ , h ∘ f₁ , h ◃ α₁) ≡ sc₂ .snd
      h≡ = secIsEq (comparisonIsEquiv po D₂) (sc₂ .snd)

    induced : Σ (D₁ → D₂) (SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd))
    induced .fst = h
    induced .snd = ≡≃SCHO _ _ h .fst h≡

  -- Uniqueness of pushout

  module _ {sc₁ sc₂ : SpanCocone} (po₁ : SpanCocone.SCIsPushout sc₁) (po₂ : SpanCocone.SCIsPushout sc₂) where
    open SpanCocone
    private
      i : Iso (D sc₁) (D sc₂)
      i = {!!}
