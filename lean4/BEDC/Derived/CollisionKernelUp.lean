import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CollisionKernelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CollisionKernelCarrier [AskSetup] [PackageSetup]
    (window fold ledger matrix moment shadow transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧ UnaryHistory matrix ∧
    UnaryHistory moment ∧ UnaryHistory shadow ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont window fold ledger ∧
        Cont ledger matrix shadow ∧ Cont moment matrix shadow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem CollisionKernelCarrier_zero_window_packet [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧ UnaryHistory matrix ∧
        UnaryHistory moment ∧ UnaryHistory shadow ∧ Cont window fold ledger ∧
          Cont ledger matrix shadow ∧ Cont moment matrix shadow ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute,
    momentRoute, provenancePkg, _nameCertPkg⟩ := carrier
  exact
    ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary, windowRoute,
      ledgerRoute, momentRoute, provenancePkg⟩

end BEDC.Derived.CollisionKernelUp
