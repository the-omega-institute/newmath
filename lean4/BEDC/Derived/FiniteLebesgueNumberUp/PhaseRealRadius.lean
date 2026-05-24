import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealRadiusAuditCarrier [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh consumerRead →
            PkgSig bundle consumerRead pkg →
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ UnaryHistory auditRead ∧ UnaryHistory phaseRead ∧
                  UnaryHistory consumerRead ∧ Cont cover window radius ∧
                    Cont route nameRow auditRead ∧ Cont auditRead radius phaseRead ∧
                      Cont phaseRead mesh consumerRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumerRead pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row auditRead ∨ hsame row phaseRead ∨
                                hsame row consumerRead)
                            (fun row : BHist =>
                              hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeNameAudit auditRadiusPhase phaseMeshConsumer consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditRadiusPhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row auditRead ∨ hsame row phaseRead ∨ hsame row consumerRead)
        (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, phaseUnary,
      consumerUnary, coverWindowRadius, routeNameAudit, auditRadiusPhase,
      phaseMeshConsumer, provenancePkg, consumerPkg, cert⟩

theorem FiniteLebesgueNumberPhaseRealRadiusConsumerCarrier [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRow continuousRow
      uniformRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh compactRow →
        Cont compactRow route continuousRow →
          Cont continuousRow nameRow uniformRow →
            PkgSig bundle uniformRow pkg →
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ UnaryHistory compactRow ∧ UnaryHistory continuousRow ∧
                  UnaryHistory uniformRow ∧ Cont cover window radius ∧
                    Cont radius mesh compactRow ∧ Cont compactRow route continuousRow ∧
                      Cont continuousRow nameRow uniformRow ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRow pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row uniformRow ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row compactRow ∨ hsame row continuousRow ∨
                                hsame row uniformRow)
                            (fun row : BHist =>
                              hsame row uniformRow ∧ PkgSig bundle uniformRow pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshCompact compactRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRow :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRow :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRow :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRow ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compactRow ∨ hsame row continuousRow ∨ hsame row uniformRow)
        (fun row : BHist => hsame row uniformRow ∧ PkgSig bundle uniformRow pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRow ⟨hsame_refl uniformRow, uniformUnary⟩
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
      exact ⟨source.left, uniformPkg⟩
  }
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, compactUnary, continuousUnary,
      uniformUnary, coverWindowRadius, radiusMeshCompact, compactRouteContinuous,
      continuousNameUniform, provenancePkg, uniformPkg, cert⟩

theorem FiniteLebesgueNumberPhaseRealRadiusConsumerExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRow continuousRow
      uniformRow outsideRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh compactRow →
        Cont compactRow route continuousRow →
          Cont continuousRow nameRow uniformRow →
            hsame outsideRead uniformRow →
              PkgSig bundle uniformRow pkg →
                UnaryHistory outsideRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row uniformRow ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactRow ∨ hsame row continuousRow ∨
                        hsame row uniformRow ∨ hsame row outsideRead)
                    (fun row : BHist => hsame row uniformRow ∧ PkgSig bundle uniformRow pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshCompact compactRouteContinuous continuousNameUniform
    sameOutsideUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRow :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRow :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRow :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have outsideUnary : UnaryHistory outsideRead :=
    unary_transport_symm uniformUnary sameOutsideUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRow ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compactRow ∨ hsame row continuousRow ∨ hsame row uniformRow ∨
            hsame row outsideRead)
        (fun row : BHist => hsame row uniformRow ∧ PkgSig bundle uniformRow pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRow ⟨hsame_refl uniformRow, uniformUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact ⟨outsideUnary, cert⟩

theorem FiniteLebesgueNumberPhaseRealRadiusConsumerStability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRow continuousRow
      uniformRow compactRow' continuousRow' uniformRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh compactRow →
        Cont compactRow route continuousRow →
          Cont continuousRow nameRow uniformRow →
            hsame compactRow' compactRow →
              hsame continuousRow' continuousRow →
                hsame uniformRow' uniformRow →
                  PkgSig bundle uniformRow pkg →
                    UnaryHistory compactRow' ∧ UnaryHistory continuousRow' ∧
                      UnaryHistory uniformRow' ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row uniformRow' ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row compactRow' ∨ hsame row continuousRow' ∨
                              hsame row uniformRow')
                          (fun row : BHist =>
                            hsame row uniformRow' ∧ PkgSig bundle uniformRow pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshCompact compactRouteContinuous continuousNameUniform
    sameCompact sameContinuous sameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRow :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRow :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRow :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have compactPrimeUnary : UnaryHistory compactRow' :=
    unary_transport_symm compactUnary sameCompact
  have continuousPrimeUnary : UnaryHistory continuousRow' :=
    unary_transport_symm continuousUnary sameContinuous
  have uniformPrimeUnary : UnaryHistory uniformRow' :=
    unary_transport_symm uniformUnary sameUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRow' ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compactRow' ∨ hsame row continuousRow' ∨ hsame row uniformRow')
        (fun row : BHist => hsame row uniformRow' ∧ PkgSig bundle uniformRow pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRow' ⟨hsame_refl uniformRow',
        uniformPrimeUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact ⟨compactPrimeUnary, continuousPrimeUnary, uniformPrimeUnary, cert⟩

def FiniteLebesgueNumberPhaseRealRadiusAuditPacket [AskSetup] [PackageSetup]
    (cover radius mesh core stream regular real _transport _replay _provenance _nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory core ∧
    UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory real ∧
      Cont cover radius mesh ∧ Cont mesh core stream ∧ Cont stream regular real ∧
        PkgSig bundle real pkg

theorem FiniteLebesgueNumberPhaseRealRadiusAuditPacket_certificate [AskSetup]
    [PackageSetup]
    {cover radius mesh core stream regular real transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberPhaseRealRadiusAuditPacket cover radius mesh core stream regular real
        transport replay provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberPhaseRealRadiusAuditPacket cover radius mesh core stream
                regular real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨ hsame row core ∨
              hsame row stream ∨ hsame row regular ∨ hsame row real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet
  have packetSource :
      FiniteLebesgueNumberPhaseRealRadiusAuditPacket cover radius mesh core stream regular
        real transport replay provenance nameRow bundle pkg :=
    packet
  obtain ⟨_coverUnary, _radiusUnary, _meshUnary, _coreUnary, _streamUnary,
    _regularUnary, _realUnary, _coverRadiusMesh, _meshCoreStream, _streamRegularReal,
    realPkg⟩ := packet
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberPhaseRealRadiusAuditPacket cover radius mesh core stream
            regular real transport replay provenance nameRow bundle pkg) real := by
    exact ⟨hsame_refl real, packetSource⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro real sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }

end BEDC.Derived.FiniteLebesgueNumberUp
