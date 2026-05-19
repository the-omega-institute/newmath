import BEDC.Derived.ApproximationTowerResidueUp.Carrier

namespace BEDC.Derived.ApproximationTowerResidueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def ApproximationTowerResidueClassifier [AskSetup] [PackageSetup]
    (source tower classifier ledger failure recovery descent transport replay provenance
      localName source' tower' classifier' ledger' failure' recovery' descent' transport'
      replay' provenance' localName' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  ApproximationTowerResidueCarrier source tower classifier ledger failure recovery descent
      transport replay provenance localName bundle pkg ∧
    ApproximationTowerResidueCarrier source' tower' classifier' ledger' failure' recovery'
      descent' transport' replay' provenance' localName' bundle pkg ∧
      hsame source source' ∧ hsame tower tower' ∧ hsame classifier classifier' ∧
        hsame ledger ledger' ∧ hsame failure failure' ∧ hsame recovery recovery' ∧
          hsame descent descent' ∧ hsame transport transport' ∧ hsame replay replay' ∧
            hsame provenance provenance' ∧ hsame localName localName'

theorem ApproximationTowerResidueClassifier_carrier_transport [AskSetup] [PackageSetup]
    {source tower classifier ledger failure recovery descent transport replay provenance
      localName source' tower' classifier' ledger' failure' recovery' descent' transport'
      replay' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApproximationTowerResidueClassifier source tower classifier ledger failure recovery descent
        transport replay provenance localName source' tower' classifier' ledger' failure'
        recovery' descent' transport' replay' provenance' localName' bundle pkg →
      ApproximationTowerResidueCarrier source' tower' classifier' ledger' failure' recovery'
        descent' transport' replay' provenance' localName' bundle pkg ∧
        hsame source source' ∧ hsame classifier classifier' ∧ hsame failure failure' ∧
          hsame recovery recovery' ∧ hsame descent descent' ∧ hsame localName localName' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  intro classified
  obtain ⟨_carrier, carrier', sameSource, _sameTower, sameClassifier, _sameLedger,
    sameFailure, sameRecovery, sameDescent, _sameTransport, _sameReplay, _sameProvenance,
    sameLocalName⟩ := classified
  exact
    ⟨carrier', sameSource, sameClassifier, sameFailure, sameRecovery, sameDescent,
      sameLocalName⟩

end BEDC.Derived.ApproximationTowerResidueUp
