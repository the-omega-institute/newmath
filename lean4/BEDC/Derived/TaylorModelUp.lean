import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TaylorModelCarrier [AskSetup] [PackageSetup]
    (center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory jet ∧ UnaryHistory remainder ∧ UnaryHistory ledger ∧
    UnaryHistory eval ∧ UnaryHistory validated ∧ UnaryHistory readback ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ UnaryHistory sameRows ∧
        UnaryHistory route ∧ UnaryHistory endpoint ∧ hsame ledger (append jet remainder) ∧
          hsame eval (append center jet) ∧ Cont sameRows route endpoint ∧
            Cont center jet eval ∧ Cont remainder ledger readback ∧
              Cont eval readback endpoint ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem TaylorModelJetLedger_finite_transport [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      exists coefficientRead : BHist,
        UnaryHistory coefficientRead ∧ hsame coefficientRead (append jet eval) ∧
          hsame eval (append center jet) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_centerUnary, jetUnary, _remainderUnary, _ledgerUnary, evalUnary,
    _validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, _endpointUnary, _ledgerRow, evalRow, _sameRowsRoute, _evalRoute,
    _readbackRoute, _endpointRoute, pkgEndpoint, _provenancePkg, _nameCertPkg⟩ := carrier
  let coefficientRead : BHist := append jet eval
  have coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed jetUnary evalUnary (rfl : Cont jet eval coefficientRead)
  exact ⟨coefficientRead, coefficientReadUnary, rfl, evalRow, pkgEndpoint⟩

theorem TaylorModelCarrier_endpoint_closure [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      UnaryHistory eval ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
        Cont eval readback endpoint ∧ PkgSig bundle nameCert pkg := by
  intro carrier
  obtain ⟨centerUnary, jetUnary, remainderUnary, ledgerUnary, _evalUnary,
    _validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, evalRoute,
    readbackRoute, endpointRoute, _endpointPkg, _provenancePkg, nameCertPkg⟩ := carrier
  have evalClosed : UnaryHistory eval :=
    unary_cont_closed centerUnary jetUnary evalRoute
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed remainderUnary ledgerUnary readbackRoute
  have endpointClosed : UnaryHistory endpoint :=
    unary_cont_closed evalClosed readbackClosed endpointRoute
  exact ⟨evalClosed, readbackClosed, endpointClosed, endpointRoute, nameCertPkg⟩

end BEDC.Derived.TaylorModelUp
