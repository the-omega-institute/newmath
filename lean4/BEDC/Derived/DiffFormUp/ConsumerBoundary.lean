import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormWedgeDegreeLedger_consumer_boundary
    {degree degreePrime partner partnerPrime out outPrime leftLedger rightLedger tensorLedger :
      BHist} :
    DiffFormWedgeDegreeLedger degree partner out leftLedger rightLedger tensorLedger ->
      hsame degree degreePrime -> hsame partner partnerPrime -> hsame out outPrime ->
        UnaryHistory degree ∧ UnaryHistory partner ∧ UnaryHistory out ∧
          Cont degree partner out ∧
            DiffFormWedgeDegreeLedger degreePrime partnerPrime outPrime leftLedger rightLedger
              tensorLedger ∧
              hsame leftLedger rightLedger := by
  intro ledger sameDegree samePartner sameOut
  have transported :=
    DiffFormWedgeDegreeLedger_classifier_stability ledger sameDegree samePartner sameOut
  exact
    ⟨ledger.left, ledger.right.left, ledger.right.right.right.left, ledger.right.right.left,
      transported.left, transported.right⟩

end BEDC.Derived.DiffFormUp
