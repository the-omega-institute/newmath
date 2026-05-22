import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont route nameRow terminalRead ∧
      Cont terminalRead radius compactRead ∧
        Cont compactRead mesh compactNetRead ∧
          Cont compactNetRead route continuousRead ∧
            Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg

theorem FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger_certificate
    [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger cover window radius mesh
        transport route provenance nameRow terminalRead compactRead compactNetRead
        continuousRead uniformRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger cover window radius
                mesh transport route provenance nameRow terminalRead compactRead
                compactNetRead continuousRead uniformRead bundle pkg)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row compactRead ∨
              hsame row compactNetRead ∨ hsame row continuousRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame ∧
        UnaryHistory terminalRead ∧ UnaryHistory compactRead ∧ UnaryHistory compactNetRead ∧
          UnaryHistory continuousRead ∧ UnaryHistory uniformRead ∧
            Cont route nameRow terminalRead ∧ Cont terminalRead radius compactRead ∧
              Cont compactRead mesh compactNetRead ∧
                Cont compactNetRead route continuousRead ∧
                  Cont continuousRead nameRow uniformRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger cover window radius mesh
        transport route provenance nameRow terminalRead compactRead compactNetRead
        continuousRead uniformRead bundle pkg :=
    ledger
  obtain ⟨carrier, routeTerminal, terminalCompact, compactNet, netContinuous,
    continuousUniform, uniformPkg⟩ := ledger
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousUniform
  have sourceUniform :
      (fun row : BHist =>
        hsame row uniformRead ∧
          FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger cover window radius mesh
            transport route provenance nameRow terminalRead compactRead compactNetRead
            continuousRead uniformRead bundle pkg) uniformRead := by
    exact ⟨hsame_refl uniformRead, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberPhaseRealTerminalRadiusReadinessLedger cover window radius
                mesh transport route provenance nameRow terminalRead compactRead
                compactNetRead continuousRead uniformRead bundle pkg)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row compactRead ∨
              hsame row compactNetRead ∨ hsame row continuousRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, terminalUnary, compactUnary, compactNetUnary, continuousUnary, uniformUnary,
      routeTerminal, terminalCompact, compactNet, netContinuous, continuousUniform,
      provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberTerminalReadinessFaceProjection [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicFace streamFace
      regseqFace realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route radius dyadicFace →
        Cont dyadicFace window streamFace →
          Cont streamFace mesh regseqFace →
            Cont regseqFace nameRow realFace →
              PkgSig bundle realFace pkg →
                UnaryHistory dyadicFace ∧ UnaryHistory streamFace ∧
                  UnaryHistory regseqFace ∧ UnaryHistory realFace ∧
                    Cont route radius dyadicFace ∧ Cont dyadicFace window streamFace ∧
                      Cont streamFace mesh regseqFace ∧ Cont regseqFace nameRow realFace ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realFace pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row dyadicFace ∨ hsame row streamFace ∨
                                hsame row regseqFace ∨ hsame row realFace)
                            (fun row : BHist =>
                              hsame row realFace ∧ PkgSig bundle realFace pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier routeRadiusDyadic dyadicWindowStream streamMeshRegseq regseqNameReal realPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed routeUnary radiusUnary routeRadiusDyadic
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have regseqUnary : UnaryHistory regseqFace :=
    unary_cont_closed streamUnary meshUnary streamMeshRegseq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regseqUnary nameRowUnary regseqNameReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicFace ∨ hsame row streamFace ∨ hsame row regseqFace ∨
            hsame row realFace)
        (fun row : BHist => hsame row realFace ∧ PkgSig bundle realFace pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realFace ⟨hsame_refl realFace, realUnary⟩
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
      exact ⟨source.left, realPkg⟩
  }
  exact
    ⟨dyadicUnary, streamUnary, regseqUnary, realUnary, routeRadiusDyadic,
      dyadicWindowStream, streamMeshRegseq, regseqNameReal, provenancePkg, realPkg, cert⟩

theorem FiniteLebesgueNumberTerminalRadiusExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow terminalRead →
        Cont terminalRead radius compactRead →
          Cont compactRead mesh compactNetRead →
            Cont compactNetRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                PkgSig bundle uniformRead pkg →
                  UnaryHistory terminalRead ∧ UnaryHistory compactRead ∧
                    UnaryHistory compactNetRead ∧ UnaryHistory continuousRead ∧
                      UnaryHistory uniformRead ∧ Cont route nameRow terminalRead ∧
                        Cont terminalRead radius compactRead ∧
                          Cont compactRead mesh compactNetRead ∧
                            Cont compactNetRead route continuousRead ∧
                              Cont continuousRead nameRow uniformRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row uniformRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row terminalRead ∨ hsame row compactRead ∨
                                        hsame row compactNetRead ∨
                                          hsame row continuousRead ∨ hsame row uniformRead)
                                    (fun row : BHist =>
                                      hsame row uniformRead ∧
                                        PkgSig bundle uniformRead pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshNet netRouteContinuous
    continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalRead ∨ hsame row compactRead ∨ hsame row compactNetRead ∨
            hsame row continuousRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact
    ⟨terminalUnary, compactUnary, compactNetUnary, continuousUnary, uniformUnary,
      routeNameTerminal, terminalRadiusCompact, compactMeshNet, netRouteContinuous,
      continuousNameUniform, provenancePkg, uniformPkg, cert⟩

theorem FiniteLebesgueNumberPhaseRealTerminalRadiusNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead outsideRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow terminalRead →
        Cont terminalRead radius compactRead →
          Cont compactRead mesh compactNetRead →
            Cont compactNetRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                hsame outsideRead uniformRead →
                  PkgSig bundle uniformRead pkg →
                    UnaryHistory outsideRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                        (fun row : BHist => hsame row outsideRead ∨ hsame row uniformRead)
                        (fun row : BHist =>
                          hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshNet netRouteContinuous
    continuousNameUniform outsideSame uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have outsideUnary : UnaryHistory outsideRead :=
    unary_transport_symm uniformUnary outsideSame
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row outsideRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact ⟨outsideUnary, cert⟩

theorem FiniteLebesgueNumberPhaseRealTerminalRadiusChoiceFreeFinality [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead terminalRead' compactRead' compactNetRead'
      continuousRead' uniformRead' outsideRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow terminalRead →
        Cont terminalRead radius compactRead →
          Cont compactRead mesh compactNetRead →
            Cont compactNetRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                hsame terminalRead' terminalRead →
                  hsame compactRead' compactRead →
                    hsame compactNetRead' compactNetRead →
                      hsame continuousRead' continuousRead →
                        hsame uniformRead' uniformRead →
                          hsame outsideRead uniformRead' →
                            PkgSig bundle uniformRead pkg →
                              UnaryHistory terminalRead' ∧ UnaryHistory compactRead' ∧
                                UnaryHistory compactNetRead' ∧
                                  UnaryHistory continuousRead' ∧
                                    UnaryHistory uniformRead' ∧ UnaryHistory outsideRead ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row uniformRead' ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row terminalRead' ∨
                                            hsame row compactRead' ∨
                                              hsame row compactNetRead' ∨
                                                hsame row continuousRead' ∨
                                                  hsame row uniformRead' ∨
                                                    hsame row outsideRead)
                                        (fun row : BHist =>
                                          hsame row uniformRead' ∧
                                            PkgSig bundle uniformRead pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshNet netRouteContinuous
    continuousNameUniform sameTerminal sameCompact sameCompactNet sameContinuous sameUniform
    sameOutside uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have terminalPrimeUnary : UnaryHistory terminalRead' :=
    unary_transport_symm terminalUnary sameTerminal
  have compactPrimeUnary : UnaryHistory compactRead' :=
    unary_transport_symm compactUnary sameCompact
  have compactNetPrimeUnary : UnaryHistory compactNetRead' :=
    unary_transport_symm compactNetUnary sameCompactNet
  have continuousPrimeUnary : UnaryHistory continuousRead' :=
    unary_transport_symm continuousUnary sameContinuous
  have uniformPrimeUnary : UnaryHistory uniformRead' :=
    unary_transport_symm uniformUnary sameUniform
  have outsideUnary : UnaryHistory outsideRead :=
    unary_transport_symm uniformPrimeUnary sameOutside
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead' ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalRead' ∨ hsame row compactRead' ∨
            hsame row compactNetRead' ∨ hsame row continuousRead' ∨
              hsame row uniformRead' ∨ hsame row outsideRead)
        (fun row : BHist => hsame row uniformRead' ∧ PkgSig bundle uniformRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead' ⟨hsame_refl uniformRead', uniformPrimeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact
    ⟨terminalPrimeUnary, compactPrimeUnary, compactNetPrimeUnary, continuousPrimeUnary,
      uniformPrimeUnary, outsideUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
