import BEDC.Derived.KuratowskiClusterSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.KuratowskiClusterSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem KuratowskiClusterSetSequentialCompactRoute [AskSetup] [PackageSetup]
    {S F Kh Km C M B X R E T U P N compactMetricRead metricRead streamRead toleranceRead
      realRead replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TasteGate.kuratowskiClusterSetFields
        (TasteGate.KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N) =
        [S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N] ->
      Cont C M compactMetricRead ->
        Cont M X metricRead ->
          Cont X R streamRead ->
            Cont R E realRead ->
              Cont T U replayRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ Cont R E realRead)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row M ∨ hsame row X ∨ hsame row R ∨
                          hsame row E ∨ hsame row B ∨ Cont T U replayRead)
                      (fun row : BHist =>
                        hsame row realRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows _compactMetricRoute _metricRoute _streamRoute realRoute replayRoute
    provenancePkg namePkg
  cases fieldRows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead (And.intro (hsame_refl realRead) realRoute)
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr replayRoute)))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

end BEDC.Derived.KuratowskiClusterSetUp
