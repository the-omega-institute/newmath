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
    _localNameUnary, proofRefutationMeta, metaAuditReplay, transportReplayProvenance,
    _provenancePkg, localNamePkg⟩ := carrier
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

theorem LogicContradictionMetaLoopCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {proofPattern refutation metaRefusal auditGate transport replay provenance localName
      auditReplay refusalReplay namedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LogicContradictionMetaLoopCarrier proofPattern refutation metaRefusal auditGate
        transport replay provenance localName bundle pkg →
      Cont metaRefusal auditGate auditReplay →
        Cont auditReplay transport refusalReplay →
          Cont refusalReplay localName namedLedger →
            PkgSig bundle namedLedger pkg →
              UnaryHistory metaRefusal ∧ UnaryHistory auditReplay ∧
                UnaryHistory refusalReplay ∧ UnaryHistory namedLedger ∧
                  Cont metaRefusal auditGate auditReplay ∧
                    Cont auditReplay transport refusalReplay ∧
                      Cont refusalReplay localName namedLedger ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                          PkgSig bundle namedLedger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier auditRoute refusalRoute ledgerRoute ledgerPkg
  obtain ⟨proofPatternUnary, refutationUnary, auditGateUnary, transportUnary, localNameUnary,
    proofRefutationMeta, _metaAuditReplay, _transportReplayProvenance, provenancePkg,
    localNamePkg⟩ := carrier
  have metaRefusalUnary : UnaryHistory metaRefusal :=
    unary_cont_closed proofPatternUnary refutationUnary proofRefutationMeta
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed metaRefusalUnary auditGateUnary auditRoute
  have refusalReplayUnary : UnaryHistory refusalReplay :=
    unary_cont_closed auditReplayUnary transportUnary refusalRoute
  have namedLedgerUnary : UnaryHistory namedLedger :=
    unary_cont_closed refusalReplayUnary localNameUnary ledgerRoute
  exact
    ⟨metaRefusalUnary, auditReplayUnary, refusalReplayUnary, namedLedgerUnary,
      auditRoute, refusalRoute, ledgerRoute, provenancePkg, localNamePkg, ledgerPkg⟩

end BEDC.Derived.LogicContradictionMetaLoopUp
