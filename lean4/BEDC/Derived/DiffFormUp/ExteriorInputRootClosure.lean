import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormExteriorInput_root_transport_closure
    {omega domega d dplus probe probePrime tensor tensorPrime scalar scalarPrime antisym source
      omega2 domega2 d2 dplus2 probe2 probePrime2 tensor2 tensorPrime2 scalar2 scalarPrime2
      antisym2 source2 : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probePrime tensor tensorPrime
      scalar scalarPrime antisym source ->
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
    hsame probe probe2 -> hsame probePrime probePrime2 -> hsame tensor tensor2 ->
    hsame tensorPrime tensorPrime2 -> hsame scalar scalar2 -> hsame scalarPrime scalarPrime2 ->
    hsame antisym antisym2 -> hsame source source2 ->
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probePrime2 tensor2
          tensorPrime2 scalar2 scalarPrime2 antisym2 source2 ∧
        UnaryHistory omega2 ∧ UnaryHistory domega2 ∧
          Cont d2 (BHist.e1 BHist.Empty) dplus2 ∧ hsame probe2 probePrime2 ∧
            hsame tensor2 tensorPrime2 ∧ hsame scalar2 scalarPrime2 := by
  intro ledger sameOmega sameDomega sameD sameDplus sameProbe sameProbePrime sameTensor
    sameTensorPrime sameScalar sameScalarPrime sameAntisym sameSource
  have transported :
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probePrime2 tensor2
        tensorPrime2 scalar2 scalarPrime2 antisym2 source2 := by
    exact (DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise sameOmega sameDomega
      sameD sameDplus sameProbe sameProbePrime sameTensor sameTensorPrime sameScalar
      sameScalarPrime sameAntisym sameSource ledger).left
  have omegaUnary : UnaryHistory omega2 :=
    unary_transport ledger.left sameOmega
  have domegaUnary : UnaryHistory domega2 :=
    unary_transport ledger.right.left sameDomega
  have degreeRow : Cont d2 (BHist.e1 BHist.Empty) dplus2 :=
    transported.right.right.right.right.left
  exact And.intro transported
    (And.intro omegaUnary
      (And.intro domegaUnary
        (And.intro degreeRow
          (And.intro transported.right.right.right.right.right.left
            (And.intro transported.right.right.right.right.right.right.left
              transported.right.right.right.right.right.right.right.left)))))

end BEDC.Derived.DiffFormUp
