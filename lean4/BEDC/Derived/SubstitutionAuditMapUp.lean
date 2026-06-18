import BEDC.Derived.SubstitutionAuditMapUp.Core
import BEDC.Derived.SubstitutionAuditMapUp.GeneratorRouteScope

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

theorem SubstitutionAuditMapCarrier_consumer_obstruction_scope [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont route name consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row term ∨ hsame row closed ∨ hsame row shift ∨
                  hsame row substitute ∨ hsame row composition ∨ hsame row generator ∨
                    hsame row transport ∨ hsame row route ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumerRead pkg)
              hsame ∧
            UnaryHistory consumerRead ∧ Cont route name consumerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, _transportUnary, routeUnary, provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, _transportRoute, _provenanceName,
    _nameGenerator, provenancePkg, _namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed routeUnary nameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row term ∨ hsame row closed ∨ hsame row shift ∨
              hsame row substitute ∨ hsame row composition ∨ hsame row generator ∨
                hsame row transport ∨ hsame row route ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary, consumerRoute, provenancePkg, consumerPkg⟩

theorem SubstitutionAuditMapCarrier_public_export [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name replayRead
      namedRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont transport route replayRead ->
        Cont replayRead name namedRead ->
          Cont provenance name ledgerRead ->
            Cont namedRead ledgerRead publicRead ->
              PkgSig bundle namedRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row namedRead ∨ hsame row ledgerRead ∨
                            hsame row publicRead)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                        hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier replayRoute namedRoute ledgerRoute publicRoute namedPkg ledgerPkg publicPkg
  have obligation :=
    SubstitutionAuditMapCarrier_obligation_closure_package carrier replayRoute namedRoute
      ledgerRoute namedPkg ledgerPkg
  obtain ⟨_namedCert, _ledgerCert, _termUnary, _closedUnary, _shiftUnary, _substituteUnary,
    _compositionUnary, _generatorUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary⟩ := obligation
  have replayPackage :=
    SubstitutionAuditMapCarrier_replay_determinacy carrier replayRoute namedRoute namedPkg
  have ledgerPackage :=
    SubstitutionAuditMapCarrier_ledger_nonescape carrier ledgerRoute ledgerPkg
  obtain ⟨_replayCert, _transportUnaryFromReplay, _routeUnaryFromReplay, _replayUnary,
    _nameUnaryFromReplay, namedUnary, _transportRoute, _nameGeneratorFromReplay,
    _provenancePkgFromReplay, _namePkgFromReplay, _namedPkg⟩ := replayPackage
  obtain ⟨_ledgerCert, _provenanceUnary, _nameUnaryFromLedger, ledgerUnary,
    _provenanceName, _nameGeneratorFromLedger, _ledgerRoute, _provenancePkg,
    _namePkgFromLedger, _ledgerPkg⟩ := ledgerPackage
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary ledgerUnary publicRoute
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row namedRead ∨ hsame row ledgerRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SubstitutionAuditMapUp
