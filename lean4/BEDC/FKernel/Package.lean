import BEDC.FKernel.Sig

/-! Packages expose visible tokens for internally generated signatures. -/
namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

class PackageSetup [AskSetup] where
  Pkg : Type
  TokIntro : ProbeBundle ProbeName → BHist → Pkg → Prop

variable [AskSetup] [P : PackageSetup]

abbrev Pkg : Type := P.Pkg
abbrev TokIntro : ProbeBundle ProbeName → BHist → Pkg → Prop := P.TokIntro

inductive psame (bundle : ProbeBundle ProbeName) : Pkg → Pkg → Prop where
  | intro {s t : BHist} {p q : Pkg} :
      TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q

def TokUnique (bundle : ProbeBundle ProbeName) : Prop :=
  ∀ {s t : BHist} {p : Pkg}, TokIntro bundle s p → TokIntro bundle t p → hsame s t

theorem psame_sound {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q := by
  intro hp hq hst
  exact psame.intro hp hq hst

theorem psame_constructor_grounding
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q ->
      exists s : BHist, exists t : BHist,
        TokIntro bundle s p /\ TokIntro bundle t q /\ hsame s t := by
  intro hpq
  cases hpq with
  | intro hp hq hst =>
      exact Exists.intro _ (Exists.intro _ (And.intro hp (And.intro hq hst)))

structure PackagePolicy (bundle : ProbeBundle ProbeName) : Prop where
  existence : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p
  extensionality :
    ∀ {s t : BHist} {p q : Pkg}, hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q
  grounding :
    ∀ {p q : Pkg}, psame bundle p q → ∃ s : BHist, ∃ t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t

theorem packagePolicy_token_exists {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) (s : BHist) :
    exists p : Pkg, TokIntro bundle s p := by
  exact policy.existence s

theorem packagePolicy_classifies_signatures
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (psame bundle p q →
        ∃ u : BHist, ∃ v : BHist,
          TokIntro bundle u p ∧ TokIntro bundle v q ∧ hsame u v) ∧
      (hsame s t → psame bundle p q) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.grounding samePkg
  · intro sameHist
    exact policy.extensionality sameHist left right

theorem PackagePolicy_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> hsame s t -> psame bundle p q := by
  intro left right sameHist
  exact policy.extensionality sameHist left right

theorem PackagePolicy_grounding_witness {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) {p q : Pkg} :
    psame bundle p q -> exists s : BHist, exists t : BHist,
      TokIntro bundle s p /\ TokIntro bundle t q /\ hsame s t := by
  intro samePkg
  exact policy.grounding samePkg

theorem package_tokens_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) {s t : BHist} {p q : Pkg} :
    hsame s t -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q := by
  intro sameHist left right
  exact policy.extensionality sameHist left right

structure PackageTokenPolicy (bundle : ProbeBundle ProbeName) : Prop where
  soundness :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q
  reflection :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t

theorem psame_reflect {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

theorem package_reflection {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

theorem packageTokenPolicy_from_reflection
    {bundle : ProbeBundle ProbeName}
    (reflection :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) :
    PackageTokenPolicy bundle := by
  exact {
    soundness := by
      intro s t p q hp hq hst
      exact psame.intro hp hq hst
    reflection := by
      intro s t p q hp hq hpq
      exact reflection hp hq hpq
  }

theorem packageTokenPolicy_from_tokUnique {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) : PackageTokenPolicy bundle := by
  exact {
    soundness := by
      intro s t p q hp hq hst
      exact psame.intro hp hq hst
    reflection := by
      intro s t p q hp hq hpq
      cases hpq with
      | intro hp0 hq0 hst0 =>
          exact hsame_trans (tok hp hp0) (hsame_trans hst0 (hsame_symm (tok hq hq0)))
  }

theorem concrete_package_token_policy
    {bundle : ProbeBundle ProbeName}
    (reflection :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) :
    PackageTokenPolicy bundle := by
  exact packageTokenPolicy_from_reflection reflection

theorem concrete_packageTokenPolicy
    {bundle : ProbeBundle ProbeName}
    (reflection :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) :
    PackageTokenPolicy bundle := by
  exact packageTokenPolicy_from_reflection reflection

theorem psame_iff_hsame
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle →
      TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro policy left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

theorem psame_symm_under_policy
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle → TokIntro bundle s p → TokIntro bundle t q →
      psame bundle p q → psame bundle q p := by
  intro policy left right samePkg
  exact policy.soundness right left (hsame_symm (policy.reflection left right samePkg))

theorem psame_trans_under_policy
    {bundle : ProbeBundle ProbeName} {a b c : BHist} {p q r : Pkg} :
    PackageTokenPolicy bundle ->
      TokIntro bundle a p -> TokIntro bundle b q -> TokIntro bundle c r ->
      psame bundle p q -> psame bundle q r -> psame bundle p r := by
  intro policy left middle right leftSame rightSame
  exact policy.soundness left right
    (hsame_trans (policy.reflection left middle leftSame)
      (policy.reflection middle right rightSame))

omit [AskSetup] P in
theorem stable_transformations_descend_to_packages [AskSetup] [PackageSetup]
    {source target : ProbeBundle ProbeName}
    (respects :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro source s p → TokIntro source t q →
          psame source p q → psame target p q)
    {s t : BHist} {p q : Pkg} :
    TokIntro source s p → TokIntro source t q →
      psame source p q → psame target p q := by
  intro hp hq same
  exact respects hp hq same

def MinimalPackageSetup [AskSetup] : PackageSetup where
  Pkg := Unit
  TokIntro := fun _ _ _ => True

def SignaturePackageSetup [AskSetup] : PackageSetup where
  Pkg := BHist
  TokIntro := fun _ s p => hsame s p

omit P [AskSetup] in
theorem signature_package_policy [A : AskSetup] (bundle : ProbeBundle ProbeName) :
    @PackagePolicy A (@SignaturePackageSetup A) bundle := by
  letI : PackageSetup := @SignaturePackageSetup A
  exact PackagePolicy.mk
    (by
      intro s
      exact ⟨s, hsame_refl s⟩)
    (by
      intro s t p q hst hp hq
      exact psame.intro hp hq hst)
    (by
      intro p q hpq
      cases hpq with
      | intro hp hq hst =>
          exact ⟨_, _, hp, hq, hst⟩)

omit P [AskSetup] in
theorem signature_package_token_exists [A : AskSetup] (bundle : ProbeBundle ProbeName) (s : BHist) :
    ∃ p : @Pkg A (@SignaturePackageSetup A),
      @TokIntro A (@SignaturePackageSetup A) bundle s p := by
  exact ⟨s, hsame_refl s⟩

end BEDC.FKernel.Package
