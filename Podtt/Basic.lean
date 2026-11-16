def hello := "world"

-- this is contexts + subst + types + terms, 'cause I'm naughty
inductive PreTerm where
| unitCtx : PreTerm
| consCtx : PreTerm → PreTerm → PreTerm
| idSubst : PreTerm
| compSubst : PreTerm → PreTerm → PreTerm
| subst : PreTerm → PreTerm → PreTerm
| consSubst : PreTerm → PreTerm → PreTerm
| final : PreTerm
| p : PreTerm
| q : PreTerm

inductive Judgment where
| ctx : PreTerm → Judgment
| type : PreTerm → PreTerm → Judgment
| term : PreTerm → PreTerm → PreTerm → Judgment
| subst : PreTerm → PreTerm → PreTerm → Judgment
| eqCtx : PreTerm → PreTerm → Judgment
| eqType : PreTerm → PreTerm → PreTerm → Judgment
| eqTerm : PreTerm → PreTerm → PreTerm → PreTerm → Judgment
| eqSubst : PreTerm → PreTerm → PreTerm → PreTerm → Judgment

open PreTerm Judgment

notation "𝕦" => unitCtx
notation "𝕚" => idSubst
notation "‼" => final

infixl:50 "⋆" => consCtx
infixl:50 "●" => consSubst
infixl:50 "∘" => compSubst
notation t "⟦" u "⟧"=> subst t u

notation t "⊢" => (ctx t)
notation t "⊢" u "type" => (type t u)
notation t "⊢" u "⋮" v => (term t u v)
notation t "⊢" u "∷" v => (subst t u v)

notation t "⊢" u "≅" u' "type" => (eqType t u u')
notation t "⊢" u "≅" u' "⋮" v => (eqTerm t u u' v)
notation t "⊢" u "≅" u' "∷" v => (eqSubst t u u' v)

-- This is the God deriviation that mixes everything together
-- We will need some `noConfusion` all over to reduce bajillions of case splits
inductive Derivation : Judgment → Prop where
| unitCtx : Derivation (𝕦 ⊢)
| consCtx : Derivation (Γ ⊢) → Derivation (Γ ⊢ A type) → Derivation ((Γ ⋆ A) ⊢)
| substTy : Derivation (Γ ⊢ A type) → Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ ⊢ (A ⟦γ⟧) type)
| substTerm : Derivation (Γ ⊢ a ⋮ A) → Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ ⊢ (a ⟦γ⟧) ⋮ (A ⟦γ⟧))
| weak : Derivation (Γ ⊢ A type) → Derivation ((Γ ⋆ A) ⊢ p ∷ Γ)
| id : Derivation (Γ ⊢) → Derivation (Γ ⊢ 𝕚 ∷ Γ)
| comp : Derivation (Γ₂ ⊢ γ₁ ∷ Γ₁) → Derivation (Γ₁ ⊢ γ₀ ∷ Γ₀) → Derivation (Γ₂ ⊢ (γ₀ ∘ γ₁) ∷ Γ₀)
| var : Derivation (Γ ⊢ A type) → Derivation ((Γ ⋆ A) ⊢ q ⋮ (A ⟦p⟧))
| extend : Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Γ ⊢ A type) → Derivation (Δ ⊢ a ⋮ (A ⟦γ⟧)) →
  Derivation (Δ ⊢ (γ ● a) ∷ (Γ ⋆ A))
| final : Derivation (Γ ⊢) → Derivation (Γ ⊢ ‼ ∷ 𝕦)
| idcomp₁ : Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ ⊢ (γ ∘ 𝕚) ≅ γ ∷ Γ)
| idcomp₂ : Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ ⊢ (𝕚 ∘ γ) ≅ γ ∷ Γ)
| idassoc : Derivation (Γ₃ ⊢ γ₂ ∷ Γ₂) → Derivation (Γ₂ ⊢ γ₁ ∷ Γ₁) → Derivation (Γ₁ ⊢ γ₀ ∷ Γ₀) →
  Derivation (Γ₃ ⊢ (γ₀ ∘ (γ₁ ∘ γ₂)) ≅ ((γ₀ ∘ γ₁) ∘ γ₂) ∷ Γ₀)
| idType : Derivation (Γ ⊢ A type) → Derivation (Γ ⊢ (A ⟦𝕚⟧) ≅ A type)
| idTerm : Derivation (Γ ⊢ a ⋮ A) → Derivation (Γ ⊢ (a ⟦𝕚⟧) ≅ a ⋮ A)
| eqConcatType : Derivation (Γ₂ ⊢ γ₁ ∷ Γ₁) → Derivation (Γ₁ ⊢ γ₀ ∷ Γ₀) → Derivation (Γ₀ ⊢ A type) →
  Derivation (Γ₂ ⊢ (A ⟦γ₀ ∘ γ₁⟧) ≅ ((A ⟦γ₀⟧) ⟦γ₁⟧) type)
| eqConcatTerm : Derivation (Γ₂ ⊢ γ₁ ∷ Γ₁) → Derivation (Γ₁ ⊢ γ₀ ∷ Γ₀) → Derivation (Γ₀ ⊢ a ⋮ A) →
  Derivation (Γ₂ ⊢ (a ⟦γ₀ ∘ γ₁⟧) ≅ ((a ⟦γ₀⟧) ⟦γ₁⟧) ⋮ (A ⟦γ₀ ∘ γ₁⟧))
| eqPCons : Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Γ ⊢ A type) → Derivation (Δ ⊢ a ⋮ A⟦γ⟧) →
  Derivation (Δ ⊢ (p ∘ (γ ● a)) ≅ γ ∷ Γ)
| eqQVar : Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Γ ⊢ A type) → Derivation (Δ ⊢ a ⋮ A⟦γ⟧) →
  Derivation (Δ ⊢ q⟦γ●a⟧ ≅ a ⋮ A⟦γ⟧)
-- this one is weird
| eqPEta : Derivation (Γ ⊢ A type) → Derivation (Δ ⊢ γ ∷ (Γ ⋆ A)) →
  Derivation (Δ ⊢ γ ≅ ((p∘γ)●(q⟦γ⟧)) ∷ Γ ⋆ A)


-- Ah the infamous conversion rules
| convTerm : Derivation (Γ ⊢ a ⋮ A) → Derivation (Γ ⊢ A ≅ A' type) → Derivation (Γ ⊢ a ⋮ A')

-- context equality is a congruence relation
| reflCtx : Derivation (Γ ⊢) → Derivation (Judgment.eqCtx Γ Γ)
| symmCtx : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Judgment.eqCtx Γ' Γ)
| transCtx : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Judgment.eqCtx Γ' Γ'') → Derivation (Judgment.eqCtx Γ Γ'')
| ctxCongr : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A type) → Derivation (Γ' ⊢ A type) →
  Derivation (Judgment.eqCtx (Γ ⋆ A) (Γ' ⋆ A))
| ctxCongrType : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A ≅ A' type) →
  Derivation (Judgment.eqCtx (Γ ⋆ A) (Γ' ⋆ A'))

-- we need like 50 rules to make equality a congruence relation
| reflType : Derivation (Γ ⊢ A type) → Derivation (Γ ⊢ A ≅ A type)
| symmType : Derivation (Γ ⊢ A ≅ A' type) → Derivation (Γ ⊢ A' ≅ A type)
| transType : Derivation (Γ ⊢ A ≅ A' type) → Derivation (Γ ⊢ A' ≅ A'' type) → Derivation (Γ ⊢ A ≅ A'' type)
| reflSubst : Derivation (Γ ⊢ γ ∷ Δ) → Derivation (Γ ⊢ γ ≅ γ ∷ Δ)
| symmSubst : Derivation (Γ ⊢ γ ≅ γ' ∷ Δ) → Derivation (Γ ⊢ γ' ≅ γ ∷ Δ)
| transSubst : Derivation (Γ ⊢ γ ≅ γ' ∷ Δ) → Derivation (Γ ⊢ γ' ≅ γ'' ∷ Δ) → Derivation (Γ ⊢ γ ≅ γ'' ∷ Δ)
| reflTerm : Derivation (Γ ⊢ a ⋮ A) → Derivation (Γ ⊢ a ≅ a ⋮ A)
| symmTerm : Derivation (Γ ⊢ a ≅ a' ⋮ A) → Derivation (Γ ⊢ a' ≅ a ⋮ A)
| transTerm : Derivation (Γ ⊢ a ≅ a' ⋮ A) → Derivation (Γ ⊢ a' ≅ a'' ⋮ A) → Derivation (Γ ⊢ a ≅ a'' ⋮ A)
| substCongrType : Derivation (Γ₂ ⊢ γ ≅ γ' ∷ Γ₁) → Derivation (Γ₁ ⊢ A type) →
  Derivation (Γ₂ ⊢ (A ⟦γ⟧) ≅ (A ⟦γ'⟧) type)
| substCongrTerm : Derivation (Γ₂ ⊢ γ ≅ γ' ∷ Γ₁) → Derivation (Γ₁ ⊢ a ⋮ A) →
  Derivation (Γ₂ ⊢ (a ⟦γ⟧) ≅ (a ⟦γ'⟧) ⋮ (A ⟦γ⟧))
| compSubstCongr : Derivation (Γ₃ ⊢ γ₂ ≅ γ₂' ∷ Γ₂) → Derivation (Γ₂ ⊢ γ₁ ≅ γ₁' ∷ Γ₁) →
  Derivation (Γ₃ ⊢ (γ₁ ∘ γ₂) ≅ (γ₁' ∘ γ₂') ∷ Γ₁)
| consSubstCongr : Derivation (Γ₂ ⊢ γ ≅ γ' ∷ Γ₁) → Derivation (Γ₁ ⊢ A type) → Derivation (Γ₂ ⊢ a ≅ a' ⋮ (A ⟦γ⟧)) →
  Derivation (Γ₂ ⊢ (γ ● a) ≅ (γ' ● a') ∷ (Γ₁ ⋆ A))

#check Derivation.substTy
