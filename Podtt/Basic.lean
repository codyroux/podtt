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
-- Having a Prop here is a little iffy
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
| finalEta : Derivation (Γ ⊢ γ ∷ 𝕦) → Derivation (Γ ⊢ γ ≅ ‼ ∷ 𝕦)
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
| convEqTerm : Derivation (Γ ⊢ a ≅ a' ⋮ A) → Derivation (Γ ⊢ A ≅ A' type) → Derivation (Γ ⊢ a ≅ a' ⋮ A')

-- context equality is a congruence relation
| reflCtx : Derivation (Γ ⊢) → Derivation (Judgment.eqCtx Γ Γ)
| symmCtx : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Judgment.eqCtx Γ' Γ)
| transCtx : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Judgment.eqCtx Γ' Γ'') → Derivation (Judgment.eqCtx Γ Γ'')
| ctxCongr : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A type) → Derivation (Γ' ⊢ A type) →
  Derivation (Judgment.eqCtx (Γ ⋆ A) (Γ' ⋆ A))
| ctxCongrType : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A ≅ A' type) →
  Derivation (Judgment.eqCtx (Γ ⋆ A) (Γ' ⋆ A'))

-- context conversion: judgments transport along context equality
| convCtxType : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A type) → Derivation (Γ' ⊢ A type)
| convCtxTerm : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ a ⋮ A) → Derivation (Γ' ⊢ a ⋮ A)
| convCtxSubstDom : Derivation (Judgment.eqCtx Δ Δ') → Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ' ⊢ γ ∷ Γ)
| convCtxSubstCod : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Δ ⊢ γ ∷ Γ) → Derivation (Δ ⊢ γ ∷ Γ')
| convCtxEqType : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ A ≅ A' type) →
  Derivation (Γ' ⊢ A ≅ A' type)
| convCtxEqTerm : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Γ ⊢ a ≅ a' ⋮ A) →
  Derivation (Γ' ⊢ a ≅ a' ⋮ A)
| convCtxEqSubstDom : Derivation (Judgment.eqCtx Δ Δ') → Derivation (Δ ⊢ γ ≅ γ' ∷ Γ) →
  Derivation (Δ' ⊢ γ ≅ γ' ∷ Γ)
| convCtxEqSubstCod : Derivation (Judgment.eqCtx Γ Γ') → Derivation (Δ ⊢ γ ≅ γ' ∷ Γ) →
  Derivation (Δ ⊢ γ ≅ γ' ∷ Γ')

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
| eqTypeSubst : Derivation (Γ₁ ⊢ A ≅ A' type) → Derivation (Γ₂ ⊢ γ ∷ Γ₁) →
  Derivation (Γ₂ ⊢ (A ⟦γ⟧) ≅ (A' ⟦γ⟧) type)
| eqTermSubst :Derivation (Γ₁ ⊢ a ≅ a' ⋮ A) → Derivation (Γ₂ ⊢ γ ∷ Γ₁) →
  Derivation (Γ₂ ⊢ (a ⟦γ⟧) ≅ (a' ⟦γ⟧) ⋮ (A ⟦γ⟧))
| compSubstCongr : Derivation (Γ₃ ⊢ γ₂ ≅ γ₂' ∷ Γ₂) → Derivation (Γ₂ ⊢ γ₁ ≅ γ₁' ∷ Γ₁) →
  Derivation (Γ₃ ⊢ (γ₁ ∘ γ₂) ≅ (γ₁' ∘ γ₂') ∷ Γ₁)
| consSubstCongr : Derivation (Γ₂ ⊢ γ ≅ γ' ∷ Γ₁) → Derivation (Γ₁ ⊢ A type) → Derivation (Γ₂ ⊢ a ≅ a' ⋮ (A ⟦γ⟧)) →
  Derivation (Γ₂ ⊢ (γ ● a) ≅ (γ' ● a') ∷ (Γ₁ ⋆ A))

#check Sigma

def lemma_2_3_4_right (dA : Derivation <| Γ ⊢ A type) (d : Derivation <| Γ ⊢ γ ∷ Γ⋆A)
    (d' : Derivation <| Γ ⊢ p ∘ γ ≅ 𝕚 ∷ Γ) : Σ' a, Derivation (Γ ⊢ a ⋮ A) :=
  -- a := q⟦γ⟧ : A⟦p⟧⟦γ⟧ ≅ A⟦p ∘ γ⟧ ≅ A⟦𝕚⟧ ≅ A
  ⟨q⟦γ⟧, Derivation.convTerm (Derivation.substTerm (Derivation.var dA) d)
    (Derivation.transType (Derivation.symmType (Derivation.eqConcatType d (Derivation.weak dA) dA))
      (Derivation.transType (Derivation.substCongrType d' dA) (Derivation.idType dA)))⟩

def lemma_2_3_4_left (dΓ : Derivation (Γ ⊢)) (dA : Derivation <| Γ ⊢ A type) (d : Derivation (Γ ⊢ a ⋮ A)) :
    Σ' γ, Derivation (Γ ⊢ γ ∷ Γ⋆A) ∧ Derivation (Γ ⊢ p ∘ γ ≅ 𝕚 ∷ Γ) :=
  -- γ := 𝕚 ● a, using a : A ≅ A⟦𝕚⟧
  have da : Derivation (Γ ⊢ a ⋮ A⟦𝕚⟧) := Derivation.convTerm d (Derivation.symmType (Derivation.idType dA))
  ⟨𝕚 ● a, Derivation.extend (Derivation.id dΓ) dA da, Derivation.eqPCons (Derivation.id dΓ) dA da⟩

theorem lemma_2_3_5 (d₁ : Derivation <| Δ ⊢ γ ∷ Γ) (dA : Derivation <| Γ ⊢ A type)
    (d₂ : Derivation <| Δ ⊢ a ⋮ A⟦γ⟧) (d₃ : Derivation <| Ξ ⊢ δ ∷ Δ) :
    Derivation (Ξ ⊢ (γ ● a) ∘ δ ≅ (γ ∘ δ) ● (a ⟦δ⟧) ∷ Γ ⋆ A) := by
  have ga := Derivation.extend d₁ dA d₂
  have σd := Derivation.comp d₃ ga
  have dp := Derivation.weak dA
  -- p ∘ ((γ ● a) ∘ δ) ≅ γ ∘ δ
  have h1 : Derivation (Ξ ⊢ p ∘ ((γ ● a) ∘ δ) ≅ γ ∘ δ ∷ Γ) :=
    Derivation.transSubst (Derivation.idassoc d₃ ga dp)
      (Derivation.compSubstCongr (Derivation.reflSubst d₃) (Derivation.eqPCons d₁ dA d₂))
  -- types we need to convert between
  have T1 : Derivation (Ξ ⊢ (A⟦p⟧)⟦(γ ● a) ∘ δ⟧ ≅ A⟦p ∘ ((γ ● a) ∘ δ)⟧ type) :=
    Derivation.symmType (Derivation.eqConcatType σd dp dA)
  have T2 : Derivation (Ξ ⊢ (A⟦γ⟧)⟦δ⟧ ≅ A⟦p ∘ ((γ ● a) ∘ δ)⟧ type) :=
    Derivation.transType (Derivation.symmType (Derivation.eqConcatType d₃ d₁ dA))
      (Derivation.substCongrType (Derivation.symmSubst h1) dA)
  -- q⟦(γ ● a) ∘ δ⟧ ≅ a⟦δ⟧
  have h2 : Derivation (Ξ ⊢ q⟦(γ ● a) ∘ δ⟧ ≅ a⟦δ⟧ ⋮ A⟦p ∘ ((γ ● a) ∘ δ)⟧) :=
    Derivation.transTerm
      (Derivation.convEqTerm (Derivation.eqConcatTerm d₃ ga (Derivation.var dA)) T1)
      (Derivation.convEqTerm (Derivation.eqTermSubst (Derivation.eqQVar d₁ dA d₂) d₃) T2)
  exact Derivation.transSubst (Derivation.eqPEta dA σd)
    (Derivation.consSubstCongr h1 dA h2)

#check Derivation.substTy
