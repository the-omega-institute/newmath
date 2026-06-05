import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem SequentiallyCompleteMetricCauchyWindowObligation [AskSetup] [PackageSetup]
    {X S R M L D _H C P N streamRead rationalRead limitRead distanceRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X S streamRead ->
      Cont streamRead R rationalRead ->
        Cont rationalRead M limitRead ->
          Cont limitRead D distanceRead ->
            Cont distanceRead C replayRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row replayRead ∧ Cont distanceRead C replayRead)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row L ∨
                        hsame row D ∨ hsame row N ∨ Cont distanceRead C replayRead)
                    (fun row : BHist =>
                      hsame row replayRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                    hsame ∧
                    hsame rationalRead rationalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _streamRoute _rationalRoute _limitRoute _distanceRoute replayRoute provenancePkg namePkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row replayRead ∧ Cont distanceRead C replayRead)
        (fun row : BHist =>
          hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row L ∨
            hsame row D ∨ hsame row N ∨ Cont distanceRead C replayRead)
        (fun row : BHist =>
          hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead (And.intro (hsame_refl replayRead) replayRoute)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right)))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }
  exact And.intro cert (hsame_refl rationalRead)

end BEDC.Derived.SequentiallyCompleteMetricUp
