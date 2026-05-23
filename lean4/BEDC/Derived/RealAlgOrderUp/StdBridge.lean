import BEDC.Derived.RealAlgOrderUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealAlgOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealAlgOrderCarrier [AskSetup] [PackageSetup]
    (endpoint readback dyadic window apartness ledger transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory endpoint ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
    UnaryHistory window ∧ UnaryHistory apartness ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont endpoint readback dyadic ∧
          Cont dyadic window apartness ∧ Cont apartness ledger transport ∧
            Cont transport route provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem RealAlgOrderUp_StdBridge [AskSetup] [PackageSetup]
    {endpoint readback dyadic window apartness ledger transport route provenance localName
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport route
        provenance localName bundle pkg ->
      Cont endpoint readback consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport
                  route provenance localName bundle pkg ∧ hsame row ledger)
              (fun row : BHist =>
                RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport
                  route provenance localName bundle pkg ∧ hsame row ledger)
              (fun row : BHist =>
                RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport
                  route provenance localName bundle pkg ∧ hsame row ledger)
              hsame ∧
            UnaryHistory consumer ∧ Cont endpoint readback consumer ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier endpointReadbackConsumer consumerPkg
  have carrierWitness := carrier
  obtain ⟨endpointUnary, readbackUnary, _dyadicUnary, _windowUnary, _apartnessUnary,
    _ledgerUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _endpointReadbackDyadic, _dyadicWindowApartness, _apartnessLedgerTransport,
    _transportRouteProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary readbackUnary endpointReadbackConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport route
              provenance localName bundle pkg ∧ hsame row ledger)
          (fun row : BHist =>
            RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport route
              provenance localName bundle pkg ∧ hsame row ledger)
          (fun row : BHist =>
            RealAlgOrderCarrier endpoint readback dyadic window apartness ledger transport route
              provenance localName bundle pkg ∧ hsame row ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger
          (And.intro carrierWitness (hsame_refl ledger))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, consumerUnary, endpointReadbackConsumer, localNamePkg, consumerPkg⟩

end BEDC.Derived.RealAlgOrderUp
