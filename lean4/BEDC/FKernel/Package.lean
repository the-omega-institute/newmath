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

def PkgSig [AskSetup] [PackageSetup] (bundle : ProbeBundle ProbeName) (s : BHist) (p : Pkg) : Prop :=
  TokIntro bundle s p

omit [AskSetup] P in
theorem PkgSig_iff_TokIntro [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    PkgSig bundle s p <-> TokIntro bundle s p := by
  rfl

inductive psame (bundle : ProbeBundle ProbeName) : Pkg → Pkg → Prop where
  | intro {s t : BHist} {p q : Pkg} :
      TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q

def TokUnique (bundle : ProbeBundle ProbeName) : Prop :=
  ∀ {s t : BHist} {p : Pkg}, TokIntro bundle s p → TokIntro bundle t p → hsame s t

theorem TokUnique_replacement {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) {s t : BHist} {p : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t p -> hsame s t := by
  intro hs ht
  exact tok hs ht

omit [AskSetup] P in
theorem tokUnique_replacement [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) {s t : BHist} {p : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t p -> hsame s t := by
  intro left right
  exact tok left right

theorem psame_reflect_under_tok_unique {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t := by
  intro left right samePkg
  cases samePkg with
  | intro left0 right0 same0 =>
      exact hsame_trans (tok left left0) (hsame_trans same0 (hsame_symm (tok right right0)))

theorem psame_trans_under_tok_unique {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle) {p q r : Pkg} :
    psame bundle p q → psame bundle q r → psame bundle p r := by
  intro leftSame rightSame
  cases leftSame with
  | intro left middle leftHist =>
      cases rightSame with
      | intro middle0 right rightHist =>
          exact psame.intro left right (hsame_trans leftHist (hsame_trans (tok middle middle0) rightHist))

theorem psame_sound {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q := by
  intro hp hq hst
  exact psame.intro hp hq hst

theorem psame_symm_constructor
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q -> psame bundle q p := by
  intro hpq
  cases hpq with
  | intro hp hq hst =>
      exact psame.intro hq hp (hsame_symm hst)

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

theorem packagePolicy_field_witnesses {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) :
    (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) ∧
    (∀ {s t : BHist} {p q : Pkg}, hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q) ∧
    (∀ {p q : Pkg}, psame bundle p q → ∃ s : BHist, ∃ t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t) := by
  constructor
  · exact policy.existence
  · constructor
    · exact policy.extensionality
    · exact policy.grounding

omit [AskSetup] P in
theorem PackagePolicy_iff_fields [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName} :
    PackagePolicy bundle ↔
      ((∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) ∧
      (∀ {s t : BHist} {p q : Pkg}, hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q) ∧
      (∀ {p q : Pkg}, psame bundle p q → ∃ s : BHist, ∃ t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t)) := by
  constructor
  · intro policy
    exact packagePolicy_field_witnesses policy
  · intro fields
    cases fields with
    | intro existence rest =>
        cases rest with
        | intro extensionality grounding =>
            exact PackagePolicy.mk existence extensionality grounding

theorem packagePolicy_token_exists {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) (s : BHist) :
    exists p : Pkg, TokIntro bundle s p := by
  exact policy.existence s

theorem packagePolicy_nonempty_token {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) (s : BHist) : Nonempty Pkg := by
  cases policy.existence s with
  | intro p tok =>
      exact Nonempty.intro p

omit [AskSetup] P in
theorem packagePolicy_fields [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) :
    (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) ∧
    (∀ {s t : BHist} {p q : Pkg},
      hsame s t -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q) ∧
    (∀ {p q : Pkg},
      psame bundle p q -> ∃ s : BHist, ∃ t : BHist,
        TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t) := by
  constructor
  · intro s
    exact policy.existence s
  · constructor
    · intro s t p q same left right
      exact policy.extensionality same left right
    · intro p q samePkg
      exact policy.grounding samePkg

omit [AskSetup] P in
theorem packagePolicy_extensionality_witness [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    hsame s t -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q := by
  intro same left right
  exact policy.extensionality same left right

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

theorem packageTokenPolicy_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s t : BHist} {p q : Pkg} :
    hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q := by
  intro sameHist left right
  exact policy.soundness left right sameHist

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

omit [AskSetup] P in
theorem package_reflection_iff_hsame [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro left right
  exact psame_iff_hsame policy left right

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
theorem signature_package_grounding [A : AskSetup] (bundle : ProbeBundle ProbeName)
    {p q : @Pkg A (@SignaturePackageSetup A)} :
    @psame A (@SignaturePackageSetup A) bundle p q ->
      exists s : BHist, exists t : BHist,
        @TokIntro A (@SignaturePackageSetup A) bundle s p /\
          @TokIntro A (@SignaturePackageSetup A) bundle t q /\ hsame s t := by
  intro samePkg
  cases samePkg with
  | intro hp hq hst =>
      exact ⟨_, _, hp, hq, hst⟩

omit P [AskSetup] in
theorem first_concrete_package_interface [A : AskSetup] (bundle : ProbeBundle ProbeName) :
    Nonempty (@PackagePolicy A (@SignaturePackageSetup A) bundle) := by
  exact Nonempty.intro (@signature_package_policy A bundle)

omit P [AskSetup] in
theorem signature_package_token_exists [A : AskSetup] (bundle : ProbeBundle ProbeName) (s : BHist) :
    ∃ p : @Pkg A (@SignaturePackageSetup A),
      @TokIntro A (@SignaturePackageSetup A) bundle s p := by
  exact ⟨s, hsame_refl s⟩

end BEDC.FKernel.Package
