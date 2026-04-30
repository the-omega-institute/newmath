import BEDC.FKernel.Sig

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

omit [AskSetup] P in
theorem TokIntro_iff_setup_field [AskSetup] [P : PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    TokIntro bundle s p ↔ P.TokIntro bundle s p := by
  rfl

def SignatureTokenIntro [AskSetup] [PackageSetup]
    (bundle : ProbeBundle ProbeName) (s : BHist) (p : Pkg) : Prop :=
  TokIntro bundle s p

omit [AskSetup] P in
theorem SignatureTokenIntro_iff_TokIntro [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    SignatureTokenIntro bundle s p <-> TokIntro bundle s p := by
  rfl

def SignatureTokenGenerator [AskSetup] [PackageSetup] (bundle : ProbeBundle ProbeName)
    (s : BHist) : Prop :=
  ∃ p : Pkg, TokIntro bundle s p

omit [AskSetup] P in
theorem SignatureTokenGenerator_iff_exists [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} :
    SignatureTokenGenerator bundle s ↔ ∃ p : Pkg, TokIntro bundle s p := by
  rfl

def PkgSig [AskSetup] [PackageSetup] (bundle : ProbeBundle ProbeName) (s : BHist) (p : Pkg) : Prop :=
  TokIntro bundle s p

omit [AskSetup] P in
theorem PkgSig_iff_TokIntro [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    PkgSig bundle s p <-> TokIntro bundle s p := by
  rfl

omit [AskSetup] P in
theorem TokIntro_iff_PkgSig [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    TokIntro bundle s p <-> PkgSig bundle s p := by
  constructor
  · intro token
    exact token
  · intro pkg
    exact pkg

omit [AskSetup] P in
theorem PkgSig_intro_from_token [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    TokIntro bundle s p → PkgSig bundle s p := by
  intro token
  exact token

omit [AskSetup] P in
theorem TokIntro_nonempty_pkg [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    TokIntro bundle s p → Nonempty Pkg := by
  intro _
  exact Nonempty.intro p

omit [AskSetup] P in
theorem SignatureTokenIntro_nonempty_pkg [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s : BHist} {p : Pkg} :
    SignatureTokenIntro bundle s p → Nonempty Pkg := by
  intro token
  exact TokIntro_nonempty_pkg ((Iff.mp SignatureTokenIntro_iff_TokIntro) token)

inductive psame (bundle : ProbeBundle ProbeName) : Pkg → Pkg → Prop where
  | intro {s t : BHist} {p q : Pkg} :
      TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q

omit [AskSetup] P in
theorem psame_source_history_pair [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q → ∃ s : BHist, ∃ t : BHist,
      TokIntro bundle s p ∧ TokIntro bundle t q := by
  intro same
  cases same with
  | intro left right _ =>
      exact Exists.intro _ (Exists.intro _ (And.intro left right))

omit [AskSetup] P in
theorem concrete_package_sameness_policy [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> hsame s t -> psame bundle p q := by
  intro left right same
  exact psame.intro left right same

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

omit [AskSetup] P in
theorem tokUnique_replacement_symm [AskSetup] [PackageSetup] {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) {s t : BHist} {p : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t p -> hsame t s := by
  intro left right
  exact hsame_symm (tokUnique_replacement tok left right)

theorem psame_reflect_under_tok_unique {bundle : ProbeBundle ProbeName}
    (tok : TokUnique bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t := by
  intro left right samePkg
  cases samePkg with
  | intro left0 right0 same0 =>
      exact hsame_trans (tok left left0) (hsame_trans same0 (hsame_symm (tok right right0)))

omit [AskSetup] P in
theorem psame_source_hsame_under_tok_unique [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle)
    {s : BHist} {p q : Pkg} :
    TokIntro bundle s p → psame bundle p q →
      ∃ t : BHist, TokIntro bundle t q ∧ hsame s t := by
  intro source samePkg
  cases samePkg with
  | intro source0 target sameHist =>
      exact Exists.intro _ (And.intro target (hsame_trans (tok source source0) sameHist))

theorem psame_trans_under_tok_unique {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle) {p q r : Pkg} :
    psame bundle p q → psame bundle q r → psame bundle p r := by
  intro leftSame rightSame
  cases leftSame with
  | intro left middle leftHist =>
      cases rightSame with
      | intro middle0 right rightHist =>
          exact psame.intro left right (hsame_trans leftHist (hsame_trans (tok middle middle0) rightHist))

omit [AskSetup] P in
theorem psame_two_step_reflect_under_tok_unique [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle)
    {s u : BHist} {p q r : Pkg} :
    TokIntro bundle s p → TokIntro bundle u r → psame bundle p q → psame bundle q r →
      hsame s u := by
  intro left right leftSame rightSame
  exact psame_reflect_under_tok_unique tok left right
    (psame_trans_under_tok_unique tok leftSame rightSame)

theorem psame_sound {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q := by
  intro hp hq hst
  exact psame.intro hp hq hst

omit [AskSetup] P in
theorem psame_iff_hsame_under_tok_unique [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> (psame bundle p q <-> hsame s t) := by
  intro hp hq
  constructor
  · intro samePkg
    exact psame_reflect_under_tok_unique tok hp hq samePkg
  · intro sameHist
    exact psame_sound hp hq sameHist

omit [AskSetup] P in
theorem psame_hsame_directions_under_tok_unique [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q ->
      (psame bundle p q -> hsame s t) /\ (hsame s t -> psame bundle p q) := by
  intro hp hq
  constructor
  · intro samePkg
    exact psame_reflect_under_tok_unique tok hp hq samePkg
  · intro sameHist
    exact psame_sound hp hq sameHist

omit [AskSetup] P in
theorem concrete_package_equivalence_signature_grounded [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (tok : TokUnique bundle) {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro left right
  constructor
  · intro samePkg
    cases samePkg with
    | intro left0 right0 same0 =>
        exact hsame_trans (tok left left0) (hsame_trans same0 (hsame_symm (tok right right0)))
  · intro sameHist
    exact psame.intro left right sameHist

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

omit [AskSetup] P in
theorem signature_package_relation_generated_only [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q → ∃ s : BHist, ∃ t : BHist,
      TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  intro hpq
  cases hpq with
  | intro hp hq hst =>
      exact Exists.intro _ (Exists.intro _ (And.intro hp (And.intro hq hst)))

theorem psame_left_token_witness {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q → exists s : BHist, TokIntro bundle s p := by
  intro hpq
  cases hpq with
  | intro hp _ _ =>
      exact Exists.intro _ hp

omit [AskSetup] P in
theorem psame_right_token_witness [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q → ∃ t : BHist, TokIntro bundle t q := by
  intro hpq
  cases hpq with
  | intro _ hq _ =>
      exact Exists.intro _ hq

omit [AskSetup] P in
theorem psame_token_witness_pair [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q -> (exists s : BHist, TokIntro bundle s p) /\
      (exists t : BHist, TokIntro bundle t q) := by
  intro hpq
  cases hpq with
  | intro hp hq _ =>
      constructor
      · exact Exists.intro _ hp
      · exact Exists.intro _ hq

omit [AskSetup] P in
theorem psame_token_witnesses [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q -> (exists s : BHist, TokIntro bundle s p) /\
      (exists t : BHist, TokIntro bundle t q) := by
  intro hpq
  cases hpq with
  | intro hp hq _ =>
      constructor
      · exact Exists.intro _ hp
      · exact Exists.intro _ hq

theorem psame_iff_constructor_witnesses {bundle : ProbeBundle ProbeName} {p q : Pkg} :
    psame bundle p q ↔ ∃ s : BHist, ∃ t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t := by
  constructor
  · intro hpq
    cases hpq with
    | intro hp hq hst =>
        exact Exists.intro _ (Exists.intro _ (And.intro hp (And.intro hq hst)))
  · intro witnesses
    cases witnesses with
    | intro s rest =>
        cases rest with
        | intro t fields =>
            cases fields with
            | intro hp right =>
                cases right with
                | intro hq hst =>
                    exact psame.intro hp hq hst
end BEDC.FKernel.Package
