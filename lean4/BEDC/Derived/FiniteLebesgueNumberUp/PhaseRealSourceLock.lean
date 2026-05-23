import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealSourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      UnaryHistory phaseRead →
        Cont provenance phaseRead consumerRead →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row radius ∨ hsame row route ∨ hsame row consumerRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                    Cont provenance phaseRead consumerRead ∧ hsame row consumerRead)
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory consumerRead ∧ Cont cover window radius ∧
                Cont radius mesh route ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier phaseUnary provenancePhaseConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    provenanceUnary, _nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed provenanceUnary phaseUnary provenancePhaseConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row radius ∨ hsame row route ∨ hsame row consumerRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
            Cont provenance phaseRead consumerRead ∧ hsame row consumerRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, provenancePhaseConsumer, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, consumerUnary, coverWindowRadius, radiusMeshRoute, consumerPkg⟩

theorem FiniteLebesgueNumberCompactUniformSourceTriangle [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead compactRead
      continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      UnaryHistory phaseRead →
        Cont provenance phaseRead compactRead →
          Cont compactRead route continuousRead →
            Cont continuousRead nameRow uniformRead →
              PkgSig bundle uniformRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row radius ∨ hsame row compactRead ∨ hsame row uniformRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                        hsame row uniformRead)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                    UnaryHistory uniformRead ∧ Cont provenance phaseRead compactRead ∧
                      Cont compactRead route continuousRead ∧
                        Cont continuousRead nameRow uniformRead ∧
                          PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier phaseUnary provenancePhaseCompact compactRouteContinuous
    continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed provenanceUnary phaseUnary provenancePhaseCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row compactRead ∨ hsame row uniformRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              hsame row uniformRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, uniformPkg, source.left⟩
  }
  exact
    ⟨cert, compactUnary, continuousUnary, uniformUnary, provenancePhaseCompact,
      compactRouteContinuous, continuousNameUniform, uniformPkg⟩

theorem FiniteLebesgueNumberPhaseRealFourFaceSourceExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead terminalRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow phaseRead →
        Cont phaseRead terminalRead consumerRead →
          UnaryHistory terminalRead →
            PkgSig bundle consumerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row radius ∨ hsame row phaseRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                      hsame row consumerRead)
                  hsame ∧
                UnaryHistory radius ∧ UnaryHistory phaseRead ∧ UnaryHistory consumerRead ∧
                  Cont cover window radius ∧ Cont route nameRow phaseRead ∧
                    Cont phaseRead terminalRead consumerRead ∧
                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeNamePhase phaseTerminalConsumer terminalUnary consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed routeUnary nameRowUnary routeNamePhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary terminalUnary phaseTerminalConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row phaseRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, phaseUnary, consumerUnary, coverWindowRadius, routeNamePhase,
      phaseTerminalConsumer, consumerPkg⟩

theorem FiniteLebesgueNumberCompactConsumerSourceVerdict [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead terminalRead
      compactVerdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
        Cont auditRead terminalRead compactVerdict ->
          UnaryHistory terminalRead ->
            PkgSig bundle compactVerdict pkg ->
              UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
                UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
                  UnaryHistory compactVerdict ∧ Cont cover window radius ∧
                    Cont radius mesh route ∧ Cont route nameRow auditRead ∧
                      Cont auditRead terminalRead compactVerdict ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle compactVerdict pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditTerminalCompact terminalUnary compactPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have compactUnary : UnaryHistory compactVerdict :=
    unary_cont_closed auditUnary terminalUnary auditTerminalCompact
  exact
    ⟨coverUnary, radiusUnary, meshUnary, auditUnary, terminalUnary, compactUnary,
      coverWindowRadius, radiusMeshRoute, routeNameAudit, auditTerminalCompact, provenancePkg,
      compactPkg⟩

theorem FiniteLebesgueNumberCompactContinuousNonchoiceExit [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead continuousRead
      exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window compactRead →
        Cont compactRead radius continuousRead →
          Cont continuousRead mesh exitRead →
            PkgSig bundle exitRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                      hsame row mesh ∨ hsame row exitRead)
                  (fun row : BHist => hsame row exitRead ∧ PkgSig bundle exitRead pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                  UnaryHistory exitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverWindowCompact compactRadiusContinuous continuousMeshExit exitPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed coverUnary windowUnary coverWindowCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary radiusUnary compactRadiusContinuous
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed continuousUnary meshUnary continuousMeshExit
  have sourceExit :
      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row) exitRead := by
    exact ⟨hsame_refl exitRead, exitUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row mesh ∨ hsame row exitRead)
          (fun row : BHist => hsame row exitRead ∧ PkgSig bundle exitRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exitRead sourceExit
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, exitPkg⟩
  }
  exact ⟨cert, compactUnary, continuousUnary, exitUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
