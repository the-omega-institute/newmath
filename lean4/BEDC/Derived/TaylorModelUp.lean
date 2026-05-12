import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TaylorModelCarrier [AskSetup] [PackageSetup]
    (center jet remainder ledger eval validated provenance nameCert sameRows route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory jet ∧ UnaryHistory remainder ∧ UnaryHistory ledger ∧
    UnaryHistory eval ∧ UnaryHistory validated ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
        hsame ledger (append jet remainder) ∧ hsame eval (append center jet) ∧
          Cont sameRows route endpoint ∧ PkgSig bundle endpoint pkg

theorem TaylorModelJetLedger_finite_transport [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated provenance nameCert sameRows route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated provenance nameCert sameRows route
        endpoint bundle pkg ->
      exists coefficientRead : BHist,
        UnaryHistory coefficientRead ∧ hsame coefficientRead (append jet eval) ∧
          hsame eval (append center jet) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_centerUnary, jetUnary, _remainderUnary, _ledgerUnary, evalUnary,
    _validatedUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary, _routeUnary,
    _endpointUnary, _ledgerRow, evalRow, _endpointRoute, pkgEndpoint⟩ := carrier
  let coefficientRead : BHist := append jet eval
  have coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed jetUnary evalUnary (rfl : Cont jet eval coefficientRead)
  exact ⟨coefficientRead, coefficientReadUnary, rfl, evalRow, pkgEndpoint⟩

end BEDC.Derived.TaylorModelUp
