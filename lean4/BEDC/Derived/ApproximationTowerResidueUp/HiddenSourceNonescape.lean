import BEDC.Derived.ApproximationTowerResidueUp.TasteGate

namespace BEDC.Derived.ApproximationTowerResidueUp

open BEDC.FKernel.Hist

theorem ApproximationTowerResidueCarrier_hidden_source_nonescape
    {tower classifier ledger failure recovery descent transport replay provenance localName
      source' tower' classifier' ledger' failure' recovery' descent' : BHist} :
    ApproximationTowerResidueUp.mk BHist.Empty tower classifier ledger failure recovery descent
        transport replay provenance localName =
      ApproximationTowerResidueUp.mk (BHist.e0 source') tower' classifier' ledger' failure'
        recovery' descent' transport replay provenance localName ->
        False := by
  -- BEDC touchpoint anchor: BHist BMark
  intro promoted
  injection promoted with sourceEq
  cases sourceEq

end BEDC.Derived.ApproximationTowerResidueUp
