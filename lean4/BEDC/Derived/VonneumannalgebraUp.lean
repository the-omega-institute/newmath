import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VonneumannalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VonneumannalgebraBHistCarrier [AskSetup] [PackageSetup]
    (cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cstar ∧ UnaryHistory hilbert ∧ UnaryHistory operator ∧
    UnaryHistory adjoint ∧ UnaryHistory multiplication ∧ UnaryHistory weakProbe ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧
        Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
          Cont weakProbe transport endpoint ∧ PkgSig bundle endpoint pkg

theorem VonneumannalgebraBHistCarrier_weak_operator_ledger_exactness [AskSetup]
    [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakProbe transport provenance endpoint
      weakEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonneumannalgebraBHistCarrier cstar hilbert operator adjoint multiplication weakProbe
        transport provenance endpoint bundle pkg ->
      Cont weakProbe hilbert weakEndpoint ->
      UnaryHistory weakEndpoint ∧ hsame weakEndpoint (append weakProbe hilbert) ∧
        Cont cstar hilbert operator ∧ Cont operator adjoint multiplication ∧
          Cont weakProbe transport endpoint ∧ Cont weakProbe hilbert weakEndpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier weakRow
  obtain ⟨cstarUnary, hilbertUnary, _operatorUnary, _adjointUnary, _multiplicationUnary,
    weakProbeUnary, _transportUnary, _provenanceUnary, cstarHilbertRow,
    operatorAdjointRow, weakTransportRow, packageRow⟩ := carrier
  have weakEndpointUnary : UnaryHistory weakEndpoint :=
    unary_cont_closed weakProbeUnary hilbertUnary weakRow
  exact And.intro weakEndpointUnary
    (And.intro weakRow
      (And.intro cstarHilbertRow
        (And.intro operatorAdjointRow
          (And.intro weakTransportRow (And.intro weakRow packageRow)))))

end BEDC.Derived.VonneumannalgebraUp
