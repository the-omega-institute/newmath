import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem SequentiallyCompleteMetricNameCertObligations [AskSetup] [PackageSetup]
    {X S M L D H C P N metricRead sequenceRead modulusRead limitRead distanceRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      Cont X S metricRead ->
        Cont metricRead M modulusRead ->
          Cont modulusRead L limitRead ->
            Cont limitRead D distanceRead ->
              Cont distanceRead C replayRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row replayRead ∧ Cont distanceRead C replayRead)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨
                          hsame row D ∨ Cont distanceRead C replayRead)
                      (fun row : BHist =>
                        hsame row replayRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows _metricRoute _modulusRoute _limitRoute _distanceRoute replayRoute
    provenancePkg namePkg
  cases fieldRows
  exact {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

end BEDC.Derived.SequentiallyCompleteMetricUp
