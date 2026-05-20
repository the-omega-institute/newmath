import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_handoff_scope [AskSetup]
    [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          UnaryHistory provenance →
            Cont routes name criticalRead →
              Cont criticalRead provenance handoff →
                PkgSig bundle handoff pkg →
                  UnaryHistory criticalRead ∧ UnaryHistory handoff ∧
                    hsame criticalRead (append routes name) ∧
                      hsame handoff (append criticalRead provenance) ∧
                        Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary provenanceUnary routesNameCritical criticalProvenanceHandoff
    handoffPkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have criticalReadUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary routesNameCritical
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed criticalReadUnary provenanceUnary criticalProvenanceHandoff
  exact
    ⟨criticalReadUnary, handoffUnary, routesNameCritical, criticalProvenanceHandoff,
      transportsRoutesProvenance, namePkg, provenancePkg, handoffPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
