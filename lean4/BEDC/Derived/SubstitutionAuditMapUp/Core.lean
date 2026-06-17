import BEDC.Derived.SubstitutionAuditMapUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubstitutionAuditMapCarrier [AskSetup] [PackageSetup]
    (term closed shift substitute composition generator transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧ UnaryHistory substitute ∧
    UnaryHistory composition ∧ UnaryHistory generator ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        hsame term closed ∧ hsame shift substitute ∧ hsame composition generator ∧
          hsame transport route ∧ hsame provenance name ∧ hsame name generator ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem SubstitutionAuditMapCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator transport
            route provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist => hsame row generator ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row name)
        hsame ∧ UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧
          UnaryHistory substitute ∧ UnaryHistory composition ∧ UnaryHistory generator ∧
            PkgSig bundle provenance pkg := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
    generatorUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, _transportRoute, _provenanceName,
    nameGenerator, provenancePkg, _namePkg⟩ := carrier
  have sourceName :
      (fun row : BHist =>
        SubstitutionAuditMapCarrier term closed shift substitute composition generator transport
          route provenance name bundle pkg ∧ hsame row name)
        name := by
    exact And.intro carrierWitness (hsame_refl name)
  have core :
      NameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator
            transport route provenance name bundle pkg ∧ hsame row name)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro name sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowName : hsame row name := sourceRow.right
        have sameOtherName : hsame other name :=
          hsame_trans (hsame_symm same) sameRowName
        exact And.intro sourceRow.left sameOtherName
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          SubstitutionAuditMapCarrier term closed shift substitute composition generator
            transport route provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist => hsame row generator ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row name)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowGenerator : hsame row generator :=
          hsame_trans sourceRow.right nameGenerator
        have rowUnary : UnaryHistory row :=
          unary_transport nameUnary (hsame_symm sourceRow.right)
        exact And.intro rowGenerator rowUnary
      ledger_sound := by
        intro row sourceRow
        exact And.intro provenancePkg sourceRow.right
    }
  exact
    ⟨cert, termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
      generatorUnary, provenancePkg⟩

theorem SubstitutionAuditMapCarrier_positive_row_coverage [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      (UnaryHistory term ∧ UnaryHistory closed ∧ UnaryHistory shift ∧
          UnaryHistory substitute ∧ UnaryHistory composition ∧ UnaryHistory generator) ∧
        (hsame term closed ∧ hsame shift substitute ∧ hsame composition generator) ∧
          (PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg) := by
  intro carrier
  obtain ⟨termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
    generatorUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    termClosed, shiftSubstitute, compositionGenerator, _transportRoute, _provenanceName,
    _nameGenerator, provenancePkg, namePkg⟩ := carrier
  exact
    ⟨⟨termUnary, closedUnary, shiftUnary, substituteUnary, compositionUnary,
      generatorUnary⟩,
      ⟨termClosed, shiftSubstitute, compositionGenerator⟩,
      ⟨provenancePkg, namePkg⟩⟩

theorem SubstitutionAuditMapCarrier_boundary_nonescape [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name row :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      hsame row name ->
        UnaryHistory row ∧ hsame row generator ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro carrier rowName
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, _transportRoute, _provenanceName,
    nameGenerator, provenancePkg, namePkg⟩ := carrier
  have rowUnary : UnaryHistory row :=
    unary_transport nameUnary (hsame_symm rowName)
  have rowGenerator : hsame row generator :=
    hsame_trans rowName nameGenerator
  exact ⟨rowUnary, rowGenerator, provenancePkg, namePkg⟩

theorem SubstitutionAuditMapCarrier_obstruction_row_exactness [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name row :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      hsame row transport ->
        UnaryHistory row ∧ hsame row route ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro carrier rowTransport
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, transportRoute, _provenanceName,
    _nameGenerator, provenancePkg, namePkg⟩ := carrier
  have rowUnary : UnaryHistory row :=
    unary_transport transportUnary (hsame_symm rowTransport)
  have rowRoute : hsame row route :=
    hsame_trans rowTransport transportRoute
  exact ⟨rowUnary, rowRoute, provenancePkg, namePkg⟩

theorem SubstitutionAuditMapCarrier_frontier_route_nonescape [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name
      frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont route name frontierRead ->
        PkgSig bundle frontierRead pkg ->
          UnaryHistory route ∧ UnaryHistory name ∧ UnaryHistory frontierRead ∧
            hsame route transport ∧ hsame name generator ∧ Cont route name frontierRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle frontierRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier frontierRoute frontierPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, transportRoute, _provenanceName,
    nameGenerator, provenancePkg, _namePkg⟩ := carrier
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed routeUnary nameUnary frontierRoute
  exact
    ⟨routeUnary, nameUnary, frontierUnary, hsame_symm transportRoute, nameGenerator,
      frontierRoute, provenancePkg, frontierPkg⟩

theorem SubstitutionAuditMapCarrier_replay_determinacy [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont transport route replayRead ->
        Cont replayRead name namedRead ->
          PkgSig bundle namedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row transport ∨ hsame row route ∨ hsame row replayRead ∨
                    hsame row name ∨ hsame row namedRead)
                (fun row : BHist =>
                  hsame row namedRead ∧ Cont transport route replayRead ∧
                    Cont replayRead name namedRead ∧ PkgSig bundle namedRead pkg)
                hsame ∧
              UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory replayRead ∧
                UnaryHistory name ∧ UnaryHistory namedRead ∧ hsame transport route ∧
                  hsame name generator ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier replayRoute namedRoute namedPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, transportRoute, _provenanceName,
    nameGenerator, provenancePkg, namePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary routeUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nameUnary namedRoute
  have sourceAtNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row transport ∨ hsame row route ∨ hsame row replayRead ∨
              hsame row name ∨ hsame row namedRead)
          (fun row : BHist =>
            hsame row namedRead ∧ Cont transport route replayRead ∧
              Cont replayRead name namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, replayRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, transportUnary, routeUnary, replayUnary, nameUnary, namedUnary, transportRoute,
      nameGenerator, provenancePkg, namePkg, namedPkg⟩

theorem SubstitutionAuditMapCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont provenance name ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row provenance ∨ hsame row name ∨ hsame row generator ∨
                  hsame row ledgerRead)
              (fun row : BHist =>
                hsame row ledgerRead ∧ Cont provenance name ledgerRead ∧
                  PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory ledgerRead ∧
              hsame provenance name ∧ hsame name generator ∧ Cont provenance name ledgerRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier ledgerRoute ledgerPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, _transportUnary, _routeUnary, provenanceUnary, nameUnary,
    _termClosed, _shiftSubstitute, _compositionGenerator, _transportRoute, provenanceName,
    nameGenerator, provenancePkg, namePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row name ∨ hsame row generator ∨
              hsame row ledgerRead)
          (fun row : BHist =>
            hsame row ledgerRead ∧ Cont provenance name ledgerRead ∧
              PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute, ledgerPkg⟩
  }
  exact
    ⟨cert, provenanceUnary, nameUnary, ledgerUnary, provenanceName, nameGenerator,
      ledgerRoute, provenancePkg, namePkg, ledgerPkg⟩

end BEDC.Derived.SubstitutionAuditMapUp
