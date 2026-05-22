import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactContinuousTriad [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRow continuousRow
      uniformRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRow ->
        Cont compactRow route continuousRow ->
          Cont continuousRow nameRow uniformRow ->
            PkgSig bundle uniformRow pkg ->
              UnaryHistory compactRow ∧ UnaryHistory continuousRow ∧
                UnaryHistory uniformRow ∧ Cont radius mesh compactRow ∧
                  Cont compactRow route continuousRow ∧
                    Cont continuousRow nameRow uniformRow ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRow :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRow :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRow :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  exact
    ⟨compactUnary, continuousUnary, uniformUnary, radiusMeshCompact,
      compactRouteContinuous, continuousNameUniform, provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberDyadicRadiusWindowAdmissionCarrierSource [AskSetup] [PackageSetup]
    -- BEDC touchpoint anchor: BHist
    {cover window radius mesh transport route provenance nameRow radiusRead windowRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius radiusRead ->
        Cont window radius windowRead ->
          Cont route nameRow rootRead ->
            PkgSig bundle rootRead pkg ->
              UnaryHistory cover /\ UnaryHistory window /\ UnaryHistory radius /\
                UnaryHistory mesh /\ UnaryHistory radiusRead /\ UnaryHistory windowRead /\
                  UnaryHistory rootRead /\ Cont cover window radius /\
                    Cont cover radius radiusRead /\ Cont window radius windowRead /\
                      Cont route nameRow rootRead /\ PkgSig bundle provenance pkg /\
                        PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusRead windowRadiusRead routeNameRoot rootPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusRead
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, radiusReadUnary, windowReadUnary,
      rootReadUnary, coverWindowRadius, coverRadiusRead, windowRadiusRead, routeNameRoot,
      provenancePkg, rootPkg⟩

theorem FiniteLebesgueNumberCompactUniformSelectorHandoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactNetRead uniformRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactNetRead ->
        Cont compactNetRead nameRow uniformRead ->
          PkgSig bundle uniformRead pkg ->
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory compactNetRead ∧ UnaryHistory uniformRead ∧
                Cont cover window radius ∧ Cont radius mesh compactNetRead ∧
                  Cont compactNetRead nameRow uniformRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactNameUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactNetUnary nameRowUnary compactNameUniform
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, compactNetUnary, uniformUnary,
      coverWindowRadius, radiusMeshCompact, compactNameUniform, provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberOpenPhaseRootUnblockRadiusCoverage [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ UnaryHistory rootRead ∧ UnaryHistory phaseRead ∧
                  UnaryHistory consumerRead ∧ Cont cover window radius ∧
                    Cont route nameRow rootRead ∧ Cont rootRead radius phaseRead ∧
                      Cont phaseRead mesh consumerRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusPhase phaseMeshConsumer consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshConsumer
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, rootUnary, phaseUnary, consumerUnary,
      coverWindowRadius, routeNameRoot, rootRadiusPhase, phaseMeshConsumer, provenancePkg,
      consumerPkg⟩

theorem FiniteLebesgueNumberDyadicRadiusWindowAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius dyadicRead ->
        Cont dyadicRead window windowRead ->
          PkgSig bundle windowRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row dyadicRead ∨ hsame row windowRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle windowRead pkg ∧
                    hsame row windowRead)
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory dyadicRead ∧ UnaryHistory windowRead ∧
                Cont cover radius dyadicRead ∧ Cont dyadicRead window windowRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusRead dyadicWindowRead windowPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusRead
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowRead
  have sourceWindowRead :
      (fun row : BHist => hsame row windowRead ∧ UnaryHistory row) windowRead := by
    exact ⟨hsame_refl windowRead, windowReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row windowRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row dyadicRead ∨ hsame row windowRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle windowRead pkg ∧
              hsame row windowRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro windowRead sourceWindowRead
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
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, windowPkg, source.left⟩
    }
  exact
    ⟨cert, radiusUnary, dyadicUnary, windowReadUnary, coverRadiusRead, dyadicWindowRead,
      provenancePkg, windowPkg⟩

theorem FiniteLebesgueNumberRadiusCarrierSource [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius radiusRead ->
        Cont route nameRow rootRead ->
          PkgSig bundle rootRead pkg ->
            UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory radiusRead ∧
              UnaryHistory rootRead ∧ Cont cover radius radiusRead ∧
                Cont route nameRow rootRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusRead routeNameRoot rootPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  exact
    ⟨coverUnary, radiusUnary, radiusReadUnary, rootReadUnary, coverRadiusRead,
      routeNameRoot, provenancePkg, rootPkg⟩

theorem FiniteLebesgueNumberCompactUniformRadiusAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead compactRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
        Cont auditRead mesh compactRead ->
          Cont compactRead radius uniformRead ->
            PkgSig bundle uniformRead pkg ->
              UnaryHistory auditRead ∧ UnaryHistory compactRead ∧
                UnaryHistory uniformRead ∧ Cont route nameRow auditRead ∧
                  Cont auditRead mesh compactRead ∧ Cont compactRead radius uniformRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditMeshCompact compactRadiusUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed auditUnary meshUnary auditMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary radiusUnary compactRadiusUniform
  exact
    ⟨auditUnary, compactUnary, uniformUnary, routeNameAudit, auditMeshCompact,
      compactRadiusUniform, provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberRadiusRowDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead uniformRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead nameRow uniformRead ->
          PkgSig bundle uniformRead pkg ->
            UnaryHistory radius ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
              Cont radius mesh compactRead ∧ Cont compactRead nameRow uniformRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  exact
    ⟨radiusUnary, compactUnary, uniformUnary, radiusMeshCompact, compactNameUniform,
      provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberRealPhaseSourceExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead terminalRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
      Cont auditRead terminalRead consumerRead ->
      UnaryHistory terminalRead ->
      PkgSig bundle consumerRead pkg ->
        UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
          UnaryHistory mesh ∧ UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
            UnaryHistory consumerRead ∧ Cont cover window radius ∧ Cont radius mesh route ∧
              Cont route nameRow auditRead ∧ Cont auditRead terminalRead consumerRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditTerminalConsumer terminalUnary consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary terminalUnary auditTerminalConsumer
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, terminalUnary,
      consumerUnary, coverWindowRadius, radiusMeshRoute, routeNameAudit,
      auditTerminalConsumer, provenancePkg, consumerPkg⟩

theorem FiniteLebesgueNumberRootRadiusSourceDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailRead realRead sourceRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route radius tailRead →
        Cont tailRead window realRead →
          Cont realRead nameRow sourceRead →
            Cont sourceRead mesh consumerRead →
              PkgSig bundle consumerRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailRead ∨ hsame row realRead ∨
                        hsame row sourceRead ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                    UnaryHistory sourceRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier routeRadiusTail tailWindowReal realNameSource sourceMeshConsumer consumerPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed routeUnary radiusUnary routeRadiusTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary windowUnary tailWindowReal
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed realUnary nameRowUnary realNameSource
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sourceUnary meshUnary sourceMeshConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row tailRead ∨ hsame row realRead ∨
            hsame row sourceRead ∨ hsame row consumerRead)
        (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact ⟨cert, tailUnary, realUnary, sourceUnary, consumerUnary⟩


end BEDC.Derived.FiniteLebesgueNumberUp
