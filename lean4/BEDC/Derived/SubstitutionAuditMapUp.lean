import BEDC.Derived.SubstitutionAuditMapUp.Core

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubstitutionAuditMapCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name replayRead
      namedRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont transport route replayRead ->
        Cont replayRead name namedRead ->
          Cont provenance name ledgerRead ->
            PkgSig bundle namedRead pkg ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row transport ∨ hsame row route ∨ hsame row replayRead ∨
                        hsame row name ∨ hsame row namedRead)
                    (fun row : BHist =>
                      hsame row namedRead ∧ Cont transport route replayRead ∧
                        Cont replayRead name namedRead ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row provenance ∨ hsame row name ∨ hsame row generator ∨
                        hsame row ledgerRead)
                    (fun row : BHist =>
                      hsame row ledgerRead ∧ Cont provenance name ledgerRead ∧
                        PkgSig bundle ledgerRead pkg)
                    hsame ∧
                    UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧
                      UnaryHistory substitute ∧ UnaryHistory composition ∧
                        UnaryHistory generator ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                          UnaryHistory provenance ∧ UnaryHistory name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier replayRoute namedRoute ledgerRoute namedPkg ledgerPkg
  have replayPackage :=
    SubstitutionAuditMapCarrier_replay_determinacy carrier replayRoute namedRoute namedPkg
  have ledgerPackage :=
    SubstitutionAuditMapCarrier_ledger_nonescape carrier ledgerRoute ledgerPkg
  obtain ⟨replayCert, _transportUnary, _routeUnary, _replayUnary, _nameUnaryFromReplay,
    _namedUnary, _transportRoute, _nameGeneratorFromReplay, _provenancePkgFromReplay,
    _namePkgFromReplay, _namedPkg⟩ := replayPackage
  obtain ⟨ledgerCert, _provenanceUnaryFromLedger, _nameUnaryFromLedger, _ledgerUnary,
    _provenanceName, _nameGeneratorFromLedger, _ledgerRoute, _provenancePkgFromLedger,
    _namePkgFromLedger, _ledgerPkg⟩ := ledgerPackage
  obtain ⟨termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary, generatorUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, _termClosed, _shiftSubstitute,
    _compositionGenerator, _transportRouteFromCarrier, _provenanceNameFromCarrier,
    _nameGeneratorFromCarrier, _provenancePkgFromCarrier, _namePkgFromCarrier⟩ := carrier
  exact
    ⟨replayCert, ledgerCert, termUnary, closedUnary, shiftUnary, substituteUnary,
      compositionUnary, generatorUnary, transportUnary, routeUnary, provenanceUnary, nameUnary⟩

end BEDC.Derived.SubstitutionAuditMapUp
