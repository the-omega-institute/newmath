import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TaylorModelCarrier [AskSetup] [PackageSetup]
    (center jet remainder ledger evaluation readback provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory jet ∧ UnaryHistory remainder ∧ UnaryHistory ledger ∧
    UnaryHistory evaluation ∧ UnaryHistory readback ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont center jet evaluation ∧ Cont remainder ledger readback ∧
        Cont evaluation readback endpoint ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg

theorem TaylorModelCarrier_endpoint_closure [AskSetup] [PackageSetup]
    {center jet remainder ledger evaluation readback provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger evaluation readback provenance name endpoint
        bundle pkg ->
      UnaryHistory evaluation ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
        Cont evaluation readback endpoint ∧ PkgSig bundle name pkg := by
  intro carrier
  obtain ⟨centerUnary, jetUnary, remainderUnary, ledgerUnary, _evaluationUnary,
    _readbackUnary, _provenanceUnary, _nameUnary, evaluationRoute, readbackRoute,
    endpointRoute, _provenanceSig, nameSig⟩ := carrier
  have evaluationClosed : UnaryHistory evaluation :=
    unary_cont_closed centerUnary jetUnary evaluationRoute
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed remainderUnary ledgerUnary readbackRoute
  have endpointClosed : UnaryHistory endpoint :=
    unary_cont_closed evaluationClosed readbackClosed endpointRoute
  exact ⟨evaluationClosed, readbackClosed, endpointClosed, endpointRoute, nameSig⟩

end BEDC.Derived.TaylorModelUp
