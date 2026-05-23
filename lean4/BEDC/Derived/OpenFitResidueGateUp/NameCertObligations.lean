import BEDC.Derived.OpenFitResidueGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.OpenFitResidueGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem OpenFitResidueGateNameCertObligations [AskSetup] [PackageSetup]
    {T F R V C H Q P N traceFit residueVerdict classifierReplay named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F traceFit ->
      Cont R V residueVerdict ->
        Cont C Q classifierReplay ->
          Cont traceFit residueVerdict named ->
            PkgSig bundle named pkg ->
              (exists packet : OpenFitResidueGateUp,
                  packet = OpenFitResidueGateUp.mk T F R V C H Q P N) /\
                Cont T F traceFit /\
                  Cont R V residueVerdict /\
                    Cont C Q classifierReplay /\
                      Cont traceFit residueVerdict named /\
                        PkgSig bundle named pkg /\
                          SemanticNameCert
                            (fun row : BHist => hsame row named)
                            (fun row : BHist =>
                              hsame row named /\ Cont traceFit residueVerdict named)
                            (fun row : BHist => hsame row named /\ PkgSig bundle named pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro traceRoute residueRoute classifierRoute namedRoute namedPkg
  have sourceNamed : (fun row : BHist => hsame row named) named := by
    exact hsame_refl named
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row named)
        (fun row : BHist => hsame row named /\ Cont traceFit residueVerdict named)
        (fun row : BHist => hsame row named /\ PkgSig bundle named pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro named sourceNamed
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact ⟨source, namedRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source, namedPkg⟩
    }
  exact
    ⟨⟨OpenFitResidueGateUp.mk T F R V C H Q P N, rfl⟩, traceRoute, residueRoute,
      classifierRoute, namedRoute, namedPkg, cert⟩

end BEDC.Derived.OpenFitResidueGateUp
