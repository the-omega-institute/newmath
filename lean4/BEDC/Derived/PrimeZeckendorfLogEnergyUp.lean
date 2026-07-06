import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PrimeZeckendorfLogEnergyUp : Type where
  | mk
      (primeLedgerHeight zeckendorfNormal phaseShell primeSupport natBudget
        logEnergy residualOrthogonality transport replay provenance localNameCert : BHist) :
      PrimeZeckendorfLogEnergyUp

end BEDC.Derived
