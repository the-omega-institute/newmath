import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CantorSpaceCarrier [AskSetup] [PackageSetup]
    (schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory boolLedger ∧
    UnaryHistory listSpine ∧ UnaryHistory endpointExclusion ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont schedule window boolLedger ∧ Cont boolLedger listSpine endpointExclusion ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem CantorSpaceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport replay
        provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrier, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CantorSpaceUp
