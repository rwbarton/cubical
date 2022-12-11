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

transportRefl' : {A : Type ℓ} → transport refl ≡ idfun A
transportRefl' = funExt transportRefl

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

module _ {A B C : Type ℓ} (f : A → B) (g : A → C) where
  SpanCoconeOn : Type ℓ → Type ℓ
  SpanCoconeOn D = Σ[ g' ∈ (B → D) ] Σ[ f' ∈ (C → D) ] g' ∘ f ≡ f' ∘ g

  module SpanCoconeOn {D : Type ℓ} (sco : SpanCoconeOn D) where
    g' : B → D
    g' = sco .fst

    f' : C → D
    f' = sco .snd .fst

    α' : g' ∘ f ≡ f' ∘ g
    α' = sco .snd .snd

  postcomp : {D D' : Type ℓ} → (D → D') → SpanCoconeOn D → SpanCoconeOn D'
  postcomp h sco .fst = h ∘ sco .fst
  postcomp h sco .snd .fst = h ∘ sco .snd .fst
  postcomp h sco .snd .snd = h ◃ sco .snd .snd

  postcomp-id : {D : Type ℓ} → postcomp (idfun D) ≡ idfun _
  postcomp-id = refl

  postcomp-transport : {D D' : Type ℓ} (p : D ≡ D') →
    postcomp (transport p) ≡ transport (λ i → SpanCoconeOn (p i))
  postcomp-transport {D = D} {D' = D'} =
    J (λ (D' : Type ℓ) (p : D ≡ D') → postcomp (transport p) ≡ transport (cong SpanCoconeOn p))
    (cong postcomp transportRefl' ∙∙ postcomp-id ∙∙ sym transportRefl')

  module _ {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) where
    pushoutComparison : (E : Type ℓ) → (P → E) → SpanCoconeOn E
    pushoutComparison E h = postcomp h (g' , f' , α)

    record isPushout : Type (ℓ-suc ℓ) where
      no-eta-equality
      field
        comparisonIsEquiv : (E : Type ℓ) → isEquiv (pushoutComparison E)

    open isPushout

    isPropIsPushout : isProp isPushout
    comparisonIsEquiv (isPropIsPushout po po' i) =
      isPropΠ (λ E → isPropIsEquiv _) (po .comparisonIsEquiv) (po' .comparisonIsEquiv) i

  open isPushout

  -- The HIT `Pushout f g` is a pushout

  PushoutIsPushout : isPushout {P = Pushout f g} inl inr (funExt push)
  comparisonIsEquiv PushoutIsPushout E = isoToIsEquiv i
    where
      open Iso
      i : Iso (Pushout f g → E) _
      i .fun = pushoutComparison inl inr (funExt push) E
      i .inv s (inl b) = s .fst b
      i .inv s (inr c) = s .snd .fst c
      i .inv s (push a k) = s .snd .snd k a
      i .rightInv s = refl
      i .leftInv h j (inl b) = h (inl b)
      i .leftInv h j (inr c) = h (inr c)
      i .leftInv h j (push a k) = h (push a k)

  SpanCocone : Type (ℓ-suc ℓ)
  SpanCocone = Σ (Type ℓ) SpanCoconeOn

  PushoutSC : SpanCocone
  PushoutSC .fst = Pushout f g
  PushoutSC .snd .fst = inl
  PushoutSC .snd .snd .fst = inr
  PushoutSC .snd .snd .snd = funExt push

  module SpanCocone (sc : SpanCocone) where
    open SpanCoconeOn (sc .snd) public

    D : Type ℓ
    D = sc .fst

    SCIsPushout : Type (ℓ-suc ℓ)
    SCIsPushout = isPushout g' f' α'

  module _ {D₁ D₂ : Type ℓ} (sco₁ : SpanCoconeOn D₁) (sco₂ : SpanCoconeOn D₂) (h : D₁ → D₂) where
    open SpanCoconeOn sco₁ renaming (g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCoconeOn sco₂ renaming (g' to g₂ ; f' to f₂ ; α' to α₂)

    SpanCoconeHomOver : Type ℓ
    SpanCoconeHomOver =
      Σ[ pg ∈ g₂ ≡ h ∘ g₁ ] Σ[ pf ∈ h ∘ f₁ ≡ f₂ ] (pg ▹ f) ∙∙ (h ◃ α₁) ∙∙ (pf ▹ g) ≡ α₂

    ≡≃SCHO : (postcomp h sco₁ ≡ sco₂) ≃ SpanCoconeHomOver
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

  idSCHO : {D : Type ℓ} {sco : SpanCoconeOn D} → SpanCoconeHomOver sco sco (idfun D)
  idSCHO = fst (≡≃SCHO _ _ (idfun _)) refl

  compSCHO : {D₁ D₂ D₃ : Type ℓ} {sco₁ : SpanCoconeOn D₁} {sco₂ : SpanCoconeOn D₂} {sco₃ : SpanCoconeOn D₃}
    (h₁₂ : D₁ → D₂) (h₂₃ : D₂ → D₃) → SpanCoconeHomOver sco₁ sco₂ h₁₂ → SpanCoconeHomOver sco₂ sco₃ h₂₃
    → SpanCoconeHomOver sco₁ sco₃ (h₂₃ ∘ h₁₂)
  compSCHO h₁₂ h₂₃ scho₁₂ scho₂₃ =
    fst (≡≃SCHO _ _ (h₂₃ ∘ h₁₂)) (cong (postcomp h₂₃) (invEq (≡≃SCHO _ _ h₁₂) scho₁₂) ∙ (invEq (≡≃SCHO _ _ h₂₃) scho₂₃))

  -- Induced map out of the pushout

  module _ {sc₁ : SpanCocone} (po : SpanCocone.SCIsPushout sc₁) (sc₂ : SpanCocone) where
    open isPushout
    open SpanCocone sc₁ renaming (D to D₁ ; g' to g₁ ; f' to f₁ ; α' to α₁)
    open SpanCocone sc₂ renaming (D to D₂ ; g' to g₂ ; f' to f₂ ; α' to α₂)

    inducedContr : isContr (Σ (D₁ → D₂) (SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd)))
    inducedContr = subst isContr (ua (Σ-cong-equiv-snd (λ h → ≡≃SCHO _ _ h)))
      (equiv-proof (comparisonIsEquiv po D₂) (sc₂ .snd))

    induced : Σ (D₁ → D₂) (SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd))
    induced = inducedContr .fst

    inducedUniq : (h h' : D₁ → D₂)
      → SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd) h
      → SpanCoconeHomOver (sc₁ .snd) (sc₂ .snd) h'
      → h ≡ h'                  -- The `SpanCoconeHomOver`s are equal too, but we don't need this.
    inducedUniq h h' scho scho' = cong fst (isContr→isProp inducedContr (h , scho) (h' , scho'))

  -- Uniqueness of pushout (up to isomorphism / a path)

  module _ {sc₁ sc₂ : SpanCocone} (po₁ : SpanCocone.SCIsPushout sc₁) (po₂ : SpanCocone.SCIsPushout sc₂) where
    open SpanCocone
    private
      open Iso
      h₁₂ : D sc₁ → D sc₂
      h₁₂ = induced po₁ sc₂ .fst

      h₂₁ : D sc₂ → D sc₁
      h₂₁ = induced po₂ sc₁ .fst

      i : Iso (D sc₁) (D sc₂)
      i .fun = h₁₂
      i .inv = h₂₁
      i .rightInv = funExt⁻
        (inducedUniq po₂ sc₂ (h₁₂ ∘ h₂₁) (idfun (D sc₂)) (compSCHO h₂₁ h₁₂ (induced po₂ sc₁ .snd) (induced po₁ sc₂ .snd)) idSCHO)
      i .leftInv = funExt⁻
        (inducedUniq po₁ sc₁ (h₂₁ ∘ h₁₂) (idfun (D sc₁)) (compSCHO h₁₂ h₂₁ (induced po₁ sc₂ .snd) (induced po₂ sc₁ .snd)) idSCHO)

      pD : D sc₁ ≡ D sc₂
      pD = ua (isoToEquiv i)

      transport-pD : transport pD ≡ h₁₂
      transport-pD = funExt (uaβ (isoToEquiv i))

    pushoutUnique : sc₁ ≡ sc₂
    pushoutUnique = ΣPathTransport→PathΣ sc₁ sc₂
      (pD ,
       sym (postcomp-transport pD ≡$ sc₁ .snd)
       ∙ cong (λ z → postcomp z (sc₁ .snd)) transport-pD
       ∙ invEq (≡≃SCHO (sc₁ .snd) (sc₂ .snd) h₁₂) (induced po₁ sc₂ .snd))

  -- Any pushout is equal to Pushout
  pushoutIsPushout : {sc : SpanCocone} (po : SpanCocone.SCIsPushout sc) → PushoutSC ≡ sc
  pushoutIsPushout = pushoutUnique PushoutIsPushout

  -- Induction principle for pushouts:
  -- to prove a property for any pushout diagram,
  -- it suffices to prove it for Pushout.
  pushoutRec : {Z : {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) → Type ℓ'} →
    Z {P = Pushout f g} inl inr (funExt push) →
    {P : Type ℓ} (g' : B → P) (f' : C → P) (α : g' ∘ f ≡ f' ∘ g) (po : isPushout g' f' α) → Z g' f' α
  pushoutRec {Z = Z} hZ g' f' α po = subst Z' (pushoutIsPushout po) hZ'
    where
      Z' : SpanCocone → Type _
      Z' sc = Z (sc .snd .fst) (sc .snd .snd .fst) (sc .snd .snd .snd)

      hZ' : Z' PushoutSC
      hZ' = hZ
