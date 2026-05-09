import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.GelfandDualityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def GelfandDualitySpectrumPairingCarrier
    (cstar topology character evaluation rhoA rhoX provenance ledger endpoint : BHist) :
    Prop :=
  UnaryHistory cstar ∧ UnaryHistory topology ∧ UnaryHistory character ∧
    UnaryHistory evaluation ∧ hsame rhoA cstar ∧ hsame rhoX topology ∧
      Cont character evaluation ledger ∧ Cont provenance ledger endpoint

theorem GelfandDualitySpectrumPairingCarrier_source_obligation
    {cstar topology character evaluation rhoA rhoX provenance ledger endpoint : BHist} :
    GelfandDualitySpectrumPairingCarrier cstar topology character evaluation rhoA rhoX
      provenance ledger endpoint ->
      UnaryHistory cstar ∧ UnaryHistory topology ∧ UnaryHistory character ∧
        UnaryHistory evaluation ∧ hsame rhoA cstar ∧ hsame rhoX topology ∧
          Cont character evaluation ledger ∧ Cont provenance ledger endpoint ∧
            hsame endpoint (append provenance ledger) := by
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right,
      carrier.right.right.right.right.right.right.right⟩

end BEDC.Derived.GelfandDualityUp
