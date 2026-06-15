import BEDC.Derived.LogicContradictionMetaLoopUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LogicContradictionMetaLoopUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LogicContradictionMetaLoopCarrier_nonescape [AskSetup] [PackageSetup]
    {proofPattern refutation metaRefusal auditGate transport replay provenance localName
      routeRead gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LogicContradictionMetaLoopCarrier proofPattern refutation metaRefusal auditGate
        transport replay provenance localName bundle pkg →
      Cont proofPattern refutation routeRead →
        Cont routeRead metaRefusal gateRead →
          PkgSig bundle gateRead pkg →
            UnaryHistory proofPattern ∧ UnaryHistory refutation ∧
              UnaryHistory metaRefusal ∧ UnaryHistory auditGate ∧ UnaryHistory routeRead ∧
                UnaryHistory gateRead ∧ Cont proofPattern refutation routeRead ∧
                  Cont routeRead metaRefusal gateRead ∧
                    Cont metaRefusal auditGate replay ∧ Cont transport replay provenance ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle gateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier routeCont gateCont gatePkg
  obtain ⟨proofPatternUnary, refutationUnary, auditGateUnary, _transportUnary,
    proofRefutationMeta, metaAuditReplay, transportReplayProvenance, _provenancePkg,
    localNamePkg⟩ := carrier
  have metaRefusalUnary : UnaryHistory metaRefusal :=
    unary_cont_closed proofPatternUnary refutationUnary proofRefutationMeta
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed proofPatternUnary refutationUnary routeCont
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed routeUnary metaRefusalUnary gateCont
  exact
    ⟨proofPatternUnary, refutationUnary, metaRefusalUnary, auditGateUnary, routeUnary,
      gateUnary, routeCont, gateCont, metaAuditReplay, transportReplayProvenance,
      localNamePkg, gatePkg⟩

end BEDC.Derived.LogicContradictionMetaLoopUp
