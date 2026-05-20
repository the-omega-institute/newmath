import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertLedgerFailureLocalNameObligation
    [AskSetup] [PackageSetup]
    {L F N ledgerFailure localName : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L F ledgerFailure ->
      Cont ledgerFailure N localName ->
        PkgSig bundle localName pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row localName)
              (fun row : BHist => Cont ledgerFailure N row)
              (fun row : BHist => hsame row localName /\ PkgSig bundle localName pkg)
              hsame /\
            Cont L F ledgerFailure /\
              Cont ledgerFailure N localName /\ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro ledgerRoute localRoute localPkg
  have sourceLocal : (fun row : BHist => hsame row localName) localName := by
    exact hsame_refl localName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row localName)
        (fun row : BHist => Cont ledgerFailure N row)
        (fun row : BHist => hsame row localName /\ PkgSig bundle localName pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName sourceLocal
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
        exact cont_result_hsame_transport localRoute (hsame_symm source)
      ledger_sound := by
        intro _row source
        exact ⟨source, localPkg⟩
    }
  exact ⟨cert, ledgerRoute, localRoute, localPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
