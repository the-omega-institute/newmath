import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumer_source_projection_scope {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger omega
      domega probePrime tensorPrime scalarPrime : BHist}
    {probes : ProbeBundle BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
        UnaryHistory degree ->
          UnaryHistory probe ->
            UnaryHistory antisym ->
              Cont degree probe tensor ->
                Cont tensor antisym scalar ->
                  hsame ledger
                    (append degree (append probe (append tensor (append scalar antisym)))) ->
                    DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                      tensorLedger ->
                      DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime
                        tensor tensorPrime scalar scalarPrime antisym ledger ->
                        ((UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                            UnaryHistory scalar ∧
                              hsame ledger
                                (append degree
                                  (append probe (append tensor (append scalar antisym))))) ∧
                          DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                            antisym ledger degree probe tensor scalar antisym ledger) ∧
                          UnaryHistory dplus ∧
                            UnaryHistory outDegree ∧
                              Cont degree dplus outDegree ∧
                                hsame ledger rightLedger ∧
                                  UnaryHistory tensor ∧
                                    UnaryHistory scalar ∧
                                      Cont degree probe tensor ∧
                                        Cont tensor antisym scalar ∧
                                          DiffFormExteriorDerivativeLedger omega domega degree
                                            dplus probe probePrime tensor tensorPrime scalar
                                            scalarPrime antisym ledger := by
  intro probeIn scalarCarrier degreeUnary probeUnary antisymUnary tensorRoute scalarRoute ledgerRoute
    wedgeLedger derivativeLedger
  have coverage :=
    DiffFormRootDegreeClassifier_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute
  exact And.intro coverage
    (And.intro wedgeLedger.right.left
      (And.intro wedgeLedger.right.right.right.left
        (And.intro wedgeLedger.right.right.left
          (And.intro wedgeLedger.right.right.right.right.right
            (And.intro coverage.left.right.right.left
              (And.intro coverage.left.right.right.right.left
                (And.intro tensorRoute (And.intro scalarRoute derivativeLedger))))))))

end BEDC.Derived.DiffFormUp
