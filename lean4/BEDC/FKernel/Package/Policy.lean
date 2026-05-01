import BEDC.FKernel.Package.Core

namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

variable [AskSetup] [P : PackageSetup]
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
theorem packagePolicy_signature_facing_from_fields [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName}
    (fields :
      (forall s : BHist, exists p : Pkg, TokIntro bundle s p) ∧
      (forall {s t : BHist} {p q : Pkg}, hsame s t -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q) ∧
      (forall {p q : Pkg}, psame bundle p q -> exists s : BHist, exists t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t))
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> hsame s t -> psame bundle p q := by
  intro left right sameHist
  exact fields.right.left sameHist left right

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

omit [AskSetup] P in
theorem packages_classify_signatures [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q ->
      (psame bundle p q ->
        exists u : BHist, exists v : BHist,
          TokIntro bundle u p /\ TokIntro bundle v q /\ hsame u v) /\
      (hsame s t -> psame bundle p q) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.grounding samePkg
  · intro sameHist
    exact policy.extensionality sameHist left right

omit [AskSetup] P in
theorem packagePolicy_classification_directions [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (hsame s t → psame bundle p q) ∧
      (psame bundle p q →
        ∃ u : BHist, ∃ v : BHist,
          TokIntro bundle u p ∧ TokIntro bundle v q ∧ hsame u v) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.extensionality sameHist left right
  · intro samePkg
    exact policy.grounding samePkg

omit [AskSetup] P in
theorem packages_classify_signatures_directional [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q ->
      (hsame s t -> psame bundle p q) /\
      (psame bundle p q ->
        exists u : BHist, exists v : BHist,
          TokIntro bundle u p /\ TokIntro bundle v q /\ hsame u v) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.extensionality sameHist left right
  · intro samePkg
    exact policy.grounding samePkg

omit [AskSetup] P in
theorem packagePolicy_classifies_signatures_directions [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (hsame s t → psame bundle p q) ∧
      (psame bundle p q →
        ∃ u : BHist, ∃ v : BHist,
          TokIntro bundle u p ∧ TokIntro bundle v q ∧ hsame u v) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.extensionality sameHist left right
  · intro samePkg
    exact policy.grounding samePkg

omit [AskSetup] P in
theorem packagePolicy_classifies_signature_witnesses [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q ->
      (hsame s t -> psame bundle p q) ∧
      (psame bundle p q ->
        ∃ u : BHist, ∃ v : BHist,
          TokIntro bundle u p ∧ TokIntro bundle v q ∧ hsame u v) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.extensionality sameHist left right
  · intro samePkg
    exact policy.grounding samePkg

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

omit [AskSetup] P in
theorem packagePolicy_no_quotient_shortcut [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle) :
    (∀ {s t : BHist} {p q : Pkg},
      hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q) ∧
    (∀ {p q : Pkg},
      psame bundle p q → ∃ s : BHist, ∃ t : BHist,
        TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t) := by
  constructor
  · exact policy.extensionality
  · exact policy.grounding

theorem package_tokens_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) {s t : BHist} {p q : Pkg} :
    hsame s t -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q := by
  intro sameHist left right
  exact policy.extensionality sameHist left right

theorem package_tokens_are_signature_facing {bundle : ProbeBundle ProbeName}
    (policy : PackagePolicy bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> hsame s t -> psame bundle p q := by
  intro left right sameHist
  exact policy.extensionality sameHist left right
end BEDC.FKernel.Package
