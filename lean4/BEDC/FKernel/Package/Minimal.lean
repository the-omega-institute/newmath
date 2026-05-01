import BEDC.FKernel.Package.TokenPolicy

namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

variable [AskSetup] [P : PackageSetup]
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
theorem signature_package_extensionality [A : AskSetup] (bundle : ProbeBundle ProbeName) {s t p q : BHist} :
    @TokIntro A (@SignaturePackageSetup A) bundle s p →
      @TokIntro A (@SignaturePackageSetup A) bundle t q →
        hsame s t → @psame A (@SignaturePackageSetup A) bundle p q := by
  intro left right sameHist
  exact @psame.intro A (@SignaturePackageSetup A) bundle s t p q left right sameHist

omit P [AskSetup] in
theorem signature_package_extensionality_hsame [A : AskSetup] (bundle : ProbeBundle ProbeName)
    {s t p q : BHist} :
    @TokIntro A (@SignaturePackageSetup A) bundle s p →
      @TokIntro A (@SignaturePackageSetup A) bundle t q →
        hsame s t → hsame p q := by
  intro left right sameHist
  exact hsame_trans (hsame_symm left) (hsame_trans sameHist right)

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
theorem signature_package_psame_implies_hsame [A : AskSetup] (bundle : ProbeBundle ProbeName)
    {p q : @Pkg A (@SignaturePackageSetup A)} :
    @psame A (@SignaturePackageSetup A) bundle p q -> hsame p q := by
  intro samePkg
  cases samePkg with
  | intro hp hq hst =>
      exact hsame_trans (hsame_symm hp) (hsame_trans hst hq)

omit P [AskSetup] in
theorem first_concrete_package_interface [A : AskSetup] (bundle : ProbeBundle ProbeName) :
    Nonempty (@PackagePolicy A (@SignaturePackageSetup A) bundle) := by
  exact Nonempty.intro (@signature_package_policy A bundle)

omit P [AskSetup] in
theorem signature_package_token_exists [A : AskSetup] (bundle : ProbeBundle ProbeName) (s : BHist) :
    ∃ p : @Pkg A (@SignaturePackageSetup A),
      @TokIntro A (@SignaturePackageSetup A) bundle s p := by
  exact ⟨s, hsame_refl s⟩

omit P [AskSetup] in
theorem signature_package_existence [A : AskSetup] (bundle : ProbeBundle ProbeName) (s : BHist) :
    exists p : @Pkg A (@SignaturePackageSetup A),
      @TokIntro A (@SignaturePackageSetup A) bundle s p := by
  exact ⟨s, hsame_refl s⟩
end BEDC.FKernel.Package
