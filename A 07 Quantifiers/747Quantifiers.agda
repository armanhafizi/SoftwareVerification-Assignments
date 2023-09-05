module 747Quantifiers where

-- Library

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s) -- added ≤
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) -- added proj₂
open import Data.Sum using (_⊎_; inj₁; inj₂ ) -- added inj₁, inj₂
open import Function using (_∘_) -- added
open import Data.Empty using (⊥; ⊥-elim)

-- Copied from 747Isomorphism.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  constructor mk-≃  -- This has been added, not in PLFA
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _⇔_

-- Logical forall is, not surpringly, ∀.
-- Forall elimination is also function application.

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- In fact, A → B is nicer syntax for ∀ (_ : A) → B.

-- 747/PLFA exercise: ForAllDistProd (1 point)
-- Show that ∀ distributes over ×.
-- (The special case of → distributes over × was shown in the Connectives chapter.)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
proj₁ (to ∀-distrib-× R) Q = proj₁ (R Q)
proj₂ (to ∀-distrib-× R) Q = proj₂ (R Q)
from ∀-distrib-× R Q = ⟨ (proj₁ R) Q , (proj₂ R) Q ⟩
from∘to ∀-distrib-× R = refl
to∘from ∀-distrib-× R = refl

-- 747/PLFA exercise: SumForAllImpForAllSum (1 point)
-- Show that a disjunction of foralls implies a forall of disjunctions.

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ ∀B) R = inj₁ (∀B R)
⊎∀-implies-∀⊎ (inj₂ ∀C) R = inj₂ (∀C R)

-- Existential quantification can be defined as a pair:
-- a witness and a proof that the witness satisfies the property.

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- Some convenient syntax.

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Unfortunately, we can use the RHS syntax in code,
-- but the LHS will show up in displays of goal and context.

-- This is equivalent to defining a dependent record type.

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- By convention, the library uses ∃ when the domain of the bound variable is implicit.

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

-- More special syntax.

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Above we saw two ways of constructing an existential.
-- We eliminate an existential with a function that consumes the
-- witness and proof and reaches a conclusion C.

{-
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f e = {!!}

-- This is a generalization of currying (from Connectives).
-- currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = {!!}
-}

-- 747/PLFA exercise: ExistsDistSum (2 points)
-- Show that existentials distribute over disjunction.

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
to ∃-distrib-⊎ ⟨ x , inj₁ y ⟩ = inj₁ ⟨ x , y ⟩
to ∃-distrib-⊎ ⟨ x , inj₂ y ⟩ = inj₂ ⟨ x , y ⟩
from ∃-distrib-⊎ (inj₁ ⟨ x , y ⟩) = ⟨ x , (inj₁ y) ⟩
from ∃-distrib-⊎ (inj₂ ⟨ x , y ⟩) = ⟨ x , (inj₂ y) ⟩
from∘to ∃-distrib-⊎ ⟨ x , inj₁ y ⟩ = refl
from∘to ∃-distrib-⊎ ⟨ x , inj₂ y ⟩ = refl
to∘from ∃-distrib-⊎ (inj₁ ⟨ x , y ⟩) = refl
to∘from ∃-distrib-⊎ (inj₂ ⟨ x , y ⟩) = refl

-- 747/PLFA exercise: ExistsProdImpProdExists (1 point)
-- Show that existentials distribute over ×.

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
proj₁ (∃×-implies-×∃ ⟨ x , y ⟩) = ⟨ x , (proj₁ y) ⟩
proj₂ (∃×-implies-×∃ ⟨ x , y ⟩) = ⟨ x , (proj₂ y) ⟩

-- An existential example: revisiting even/odd.

-- Recall the mutually-recursive definitions of even and odd.

{-
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
-}

-- An number is even iff it is double some other number.
-- A number is odd iff is one plus double some other number.
-- Proofs below.

{-
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ e = {!!}
odd-∃ e = {!!}

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even e = {!!}
∃-odd  e = {!!}
-}

-- PLFA exercise: what if we write the arithmetic more "naturally"?
-- (Proof gets harder but is still doable).

-- 747/PLFA exercise: AltLE (3 points)
-- An alternate definition of y ≤ z.
-- (Optional exercise: Is this an isomorphism?)

suc-elim : ∀ (m n : ℕ) → suc m ≡ suc n → m ≡ n -- helper
suc-elim zero zero x = refl
suc-elim zero (suc n) ()
suc-elim (suc m) (suc .m) refl = refl

∃-≤ : ∀ {y z : ℕ} → ( (y ≤ z) ⇔ ( ∃[ x ] (y + x ≡ z) ) )
to (∃-≤ {zero} {z}) z≤n = ⟨ z , refl ⟩
to (∃-≤ {suc y} {suc z}) (s≤s R) with to (∃-≤ {y} {z}) R
... | ⟨ u , v ⟩ = ⟨ u , cong suc v ⟩
from (∃-≤ {zero} {z}) R = z≤n
from (∃-≤ {suc y} {zero}) ⟨ u , () ⟩
from (∃-≤ {suc y} {suc z}) ⟨ u , v ⟩ with ∃-≤ {y} {z}
... | record { to = to ; from = from } = s≤s (from ⟨ u , suc-elim (y + u) z v ⟩)

-- The negation of an existential is isomorphic to a universal of a negation.

{-
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = {!!}
-}

-- 747/PLFA exercise: ExistsNegImpNegForAll (1 point)
-- Existence of negation implies negation of universal.

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ {A} {B} ⟨ x , y ⟩ R = y (R x)

-- The converse cannot be proved in intuitionistic logic.

-- PLFA exercise: isomorphism between naturals and existence of canonical binary.
-- This is essentially what we did at the end of 747Isomorphism.
