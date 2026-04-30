import BEDC.FKernel.Package.Policy

namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

variable [AskSetup] [P : PackageSetup]
structure PackageTokenPolicy (bundle : ProbeBundle ProbeName) : Prop where
  soundness :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q
  reflection :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t

omit [AskSetup] P in
theorem PackageTokenPolicy_iff_fields [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} :
    PackageTokenPolicy bundle ↔
      ((∀ {s t : BHist} {p q : Pkg},
          TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q) ∧
        (∀ {s t : BHist} {p q : Pkg},
          TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t)) := by
  constructor
  · intro policy
    constructor
    · exact policy.soundness
    · exact policy.reflection
  · intro fields
    cases fields with
    | intro soundness reflection =>
        exact PackageTokenPolicy.mk soundness reflection

theorem PackageTokenPolicy_iff_soundness_reflection {bundle : ProbeBundle ProbeName} :
    PackageTokenPolicy bundle ↔
      ((∀ {s t : BHist} {p q : Pkg},
          TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q) ∧
        (∀ {s t : BHist} {p q : Pkg},
          TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t)) := by
  constructor
  · intro policy
    constructor
    · intro s t p q left right sameHist
      exact policy.soundness left right sameHist
    · intro s t p q left right samePkg
      exact policy.reflection left right samePkg
  · intro fields
    cases fields with
    | intro soundness reflection =>
        exact PackageTokenPolicy.mk soundness reflection

omit [AskSetup] P in
theorem PackageTokenPolicy_fields [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle) :
    (∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q) ∧
    (∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) := by
  constructor
  · exact policy.soundness
  · exact policy.reflection

theorem packageTokenPolicy_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s t : BHist} {p q : Pkg} :
    hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q := by
  intro sameHist left right
  exact policy.soundness left right sameHist

omit [AskSetup] P in
theorem packageTokenPolicy_soundness_field [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q := by
  intro left right sameHist
  exact policy.soundness left right sameHist

omit [AskSetup] P in
theorem packageTokenPolicy_reflection_field [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t := by
  intro left right samePkg
  exact policy.reflection left right samePkg

theorem packageTokenPolicy_psame_refl_on_introduced {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s : BHist} {p : Pkg} :
    TokIntro bundle s p → psame bundle p p := by
  intro tok
  exact policy.soundness tok tok (hsame_refl s)

theorem psame_reflect {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

theorem package_reflection {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

omit [AskSetup] P in
theorem package_reflection_forward [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p ∧ TokIntro bundle t q ∧ psame bundle p q → hsame s t := by
  intro packed
  cases packed with
  | intro left rest =>
      cases rest with
      | intro right samePkg =>
          exact policy.reflection left right samePkg

theorem concrete_package_completeness_policy_grounded
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t := by
  intro hp hq hpq
  exact policy.reflection hp hq hpq

omit [AskSetup] P in
theorem package_completeness_reflection_field [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t := by
  intro left right samePkg
  exact policy.reflection left right samePkg

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
theorem PackageTokenPolicy_iff_classifies_introduced [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} :
    PackageTokenPolicy bundle ↔
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  constructor
  · intro policy
    intro s t p q left right
    exact psame_iff_hsame policy left right
  · intro classifies
    exact {
      soundness := by
        intro s t p q left right sameHist
        exact (classifies left right).mpr sameHist
      reflection := by
        intro s t p q left right samePkg
        exact (classifies left right).mp samePkg
    }

omit [AskSetup] P in
theorem exact_signature_package [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> (psame bundle p q ↔ hsame s t) := by
  intro left right
  exact psame_iff_hsame policy left right

omit [AskSetup] P in
theorem PackageTokenPolicy_sound_complete [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (hsame s t → psame bundle p q) ∧ (psame bundle p q → hsame s t) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.soundness left right sameHist
  · intro samePkg
    exact policy.reflection left right samePkg

omit [AskSetup] P in
theorem packageTokenPolicy_classifies_introduced_signatures
    [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro left right
  exact psame_iff_hsame policy left right

omit [AskSetup] P in
theorem packageTokenPolicy_compares_introduced_by_psame
    [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

omit [AskSetup] P in
theorem packages_classify_introduced_signatures [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg}
    (policy : PackageTokenPolicy bundle) :
    TokIntro bundle s p -> TokIntro bundle t q -> (psame bundle p q <-> hsame s t) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

omit [AskSetup] P in
theorem packages_classify_introduced_signatures_directional [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg}
    (policy : PackageTokenPolicy bundle) :
    TokIntro bundle s p → TokIntro bundle t q →
      (psame bundle p q → hsame s t) ∧ (hsame s t → psame bundle p q) := by
  intro left right
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

theorem packageTokenPolicy_psame_symm_on_introduced {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> psame bundle q p := by
  intro left right samePkg
  exact policy.soundness right left (hsame_symm (policy.reflection left right samePkg))

omit [AskSetup] P in
theorem packageTokenPolicy_reflection_symmetry_pair [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q ->
      hsame s t /\ psame bundle q p := by
  intro left right samePkg
  have sameHist : hsame s t := policy.reflection left right samePkg
  exact And.intro sameHist (policy.soundness right left (hsame_symm sameHist))

theorem psame_trans_under_policy
    {bundle : ProbeBundle ProbeName} {a b c : BHist} {p q r : Pkg} :
    PackageTokenPolicy bundle ->
      TokIntro bundle a p -> TokIntro bundle b q -> TokIntro bundle c r ->
      psame bundle p q -> psame bundle q r -> psame bundle p r := by
  intro policy left middle right leftSame rightSame
  exact policy.soundness left right
    (hsame_trans (policy.reflection left middle leftSame)
      (policy.reflection middle right rightSame))

theorem packageTokenPolicy_psame_trans_on_introduced {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) {a b c : BHist} {p q r : Pkg} :
    TokIntro bundle a p -> TokIntro bundle b q -> TokIntro bundle c r ->
      psame bundle p q -> psame bundle q r -> psame bundle p r := by
  intro left middle right leftSame rightSame
  exact psame_trans_under_policy policy left middle right leftSame rightSame

omit [AskSetup] P in
theorem packageTokenPolicy_psame_chain_three_on_introduced [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {a b c d : BHist} {p q r s : Pkg} :
    TokIntro bundle a p → TokIntro bundle b q → TokIntro bundle c r →
      TokIntro bundle d s → psame bundle p q → psame bundle q r →
        psame bundle r s → psame bundle p s := by
  intro left middle right last leftSame middleSame rightSame
  have firstChain : psame bundle p r :=
    packageTokenPolicy_psame_trans_on_introduced policy left middle right leftSame middleSame
  exact packageTokenPolicy_psame_trans_on_introduced policy left right last firstChain rightSame

omit [AskSetup] P in
theorem packageTokenPolicy_two_step_reflect_on_introduced [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {a b c : BHist} {p q r : Pkg} :
    TokIntro bundle a p → TokIntro bundle b q → TokIntro bundle c r →
      psame bundle p q → psame bundle q r → hsame a c := by
  intro left middle right leftSame rightSame
  exact policy.reflection left right
    (psame_trans_under_policy policy left middle right leftSame rightSame)

theorem packageTokenPolicy_psame_equivalence_on_introduced {bundle : ProbeBundle ProbeName}
    (policy : PackageTokenPolicy bundle) :
    (forall {s : BHist} {p : Pkg}, TokIntro bundle s p -> psame bundle p p) /\
    (forall {s t : BHist} {p q : Pkg}, TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> psame bundle q p) /\
    (forall {a b c : BHist} {p q r : Pkg}, TokIntro bundle a p -> TokIntro bundle b q -> TokIntro bundle c r -> psame bundle p q -> psame bundle q r -> psame bundle p r) := by
  constructor
  · intro s p tok
    exact policy.soundness tok tok (hsame_refl s)
  · constructor
    · intro s t p q left right samePkg
      exact psame_symm_under_policy policy left right samePkg
    · intro a b c p q r left middle right leftSame rightSame
      exact psame_trans_under_policy policy left middle right leftSame rightSame

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
end BEDC.FKernel.Package
