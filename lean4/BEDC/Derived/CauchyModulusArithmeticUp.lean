import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusArithmeticCarrier [AskSetup] [PackageSetup]
    (stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream0 ∧ UnaryHistory stream1 ∧ UnaryHistory modulus0 ∧
    UnaryHistory modulus1 ∧ UnaryHistory meet ∧ UnaryHistory sum ∧
      UnaryHistory product ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
          Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
            Cont meet dyadic product ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem CauchyModulusArithmeticCarrier_sum_meet_route_closure [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic sumRead ->
        UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sum ∧ UnaryHistory sumRead ∧
          Cont meet dyadic sum ∧ Cont meet dyadic sumRead ∧ Cont window readback sealRow := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sumReadRoute
  exact
    match carrier with
    | ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
        sumUnary, _productUnary, dyadicUnary, _windowUnary, _readbackUnary, _sealUnary,
        _transportUnary, _meetRoute, sumRoute, _productRoute, windowRoute,
        _transportRoute, _pkgSig⟩ =>
        ⟨meetUnary, dyadicUnary, sumUnary, unary_cont_closed meetUnary dyadicUnary sumReadRoute,
          sumRoute, sumReadRoute, windowRoute⟩

end BEDC.Derived.CauchyModulusArithmeticUp
