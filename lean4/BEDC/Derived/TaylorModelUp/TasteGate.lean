import BEDC.Derived.TaylorModelUp

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TaylorModelFiniteJet_transport [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint window coefficientRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      UnaryHistory window ->
        Cont jet window coefficientRead ->
          Cont coefficientRead eval consumerRead ->
            UnaryHistory coefficientRead ∧ UnaryHistory consumerRead ∧
              hsame eval (append center jet) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier windowUnary jetWindowRead coefficientEvalRead
  obtain ⟨_centerUnary, jetUnary, _remainderUnary, _ledgerUnary, evalUnary,
    _validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, _endpointUnary, _ledgerRow, evalRow, _sameRowsRoute, _evalRoute,
    _readbackRoute, _endpointRoute, endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed jetUnary windowUnary jetWindowRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed coefficientReadUnary evalUnary coefficientEvalRead
  exact ⟨coefficientReadUnary, consumerReadUnary, evalRow, endpointPkg⟩

end BEDC.Derived.TaylorModelUp
