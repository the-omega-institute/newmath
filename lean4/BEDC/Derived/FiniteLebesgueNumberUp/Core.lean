import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberCarrier [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory nameRow ∧ Cont cover window radius ∧ Cont radius mesh route ∧
        Cont route nameRow provenance ∧ PkgSig bundle provenance pkg

theorem FiniteLebesgueNumberCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance
                    nameRow bundle pkg ∧
                  hsame row nameRow)
              (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
                  Cont route nameRow auditRead)
              hsame ∧
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory auditRead ∧ Cont cover window radius ∧
                Cont radius mesh route ∧ Cont route nameRow auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameAudit auditPkg
  have carrierPacket :
      FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance
                nameRow bundle pkg ∧
              hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
              Cont route nameRow auditRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := by
          exact Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
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
          exact And.intro source.left
            (hsame_trans (hsame_symm sameRows) source.right)
      }
      pattern_sound := by
        intro _row source
        exact And.intro source.right (unary_transport nameRowUnary (hsame_symm source.right))
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg (And.intro source.right routeNameAudit)
    }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary,
      coverWindowRadius, radiusMeshRoute, routeNameAudit, provenancePkg, auditPkg⟩

theorem FiniteLebesgueNumberDyadicCoverHandoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
            UnaryHistory mesh ∧ UnaryHistory auditRead ∧ Cont cover window radius ∧
              Cont radius mesh route ∧ Cont route nameRow auditRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit auditPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, coverWindowRadius,
      radiusMeshRoute, routeNameAudit, provenancePkg, auditPkg⟩

theorem FiniteLebesgueNumberRadiusTransport [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow transportedRadius
      radiusAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      hsame transportedRadius radius →
        Cont transportedRadius mesh radiusAudit →
          PkgSig bundle provenance pkg →
            UnaryHistory transportedRadius ∧ UnaryHistory radiusAudit ∧
              SemanticNameCert
                (fun row : BHist => hsame row radiusAudit ∧ UnaryHistory row)
                (fun row : BHist => hsame row transportedRadius ∨ hsame row radiusAudit)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ hsame row radiusAudit)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameTransported radiusAuditRoute provenancePkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _carrierPkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRadius :=
    unary_transport_symm radiusUnary sameTransported
  have radiusAuditUnary : UnaryHistory radiusAudit :=
    unary_cont_closed transportedUnary meshUnary radiusAuditRoute
  have sourceAudit :
      (fun row : BHist => hsame row radiusAudit ∧ UnaryHistory row) radiusAudit := by
    exact ⟨hsame_refl radiusAudit, radiusAuditUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row radiusAudit ∧ UnaryHistory row)
        (fun row : BHist => hsame row transportedRadius ∨ hsame row radiusAudit)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row radiusAudit)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro radiusAudit sourceAudit
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
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.left⟩
    }
  exact ⟨transportedUnary, radiusAuditUnary, cert⟩

theorem FiniteLebesgueNumberCoverCellReadbackTotality [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow windowRead coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius windowRead ->
        Cont windowRead mesh coverCell ->
          PkgSig bundle coverCell pkg ->
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory windowRead ∧ UnaryHistory coverCell ∧
                Cont cover window radius ∧ Cont window radius windowRead ∧
                  Cont windowRead mesh coverCell ∧ Cont radius mesh route ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle coverCell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRadiusRead readMeshCell coverCellPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed windowReadUnary meshUnary readMeshCell
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, windowReadUnary, coverCellUnary,
      coverWindowRadius, windowRadiusRead, readMeshCell, radiusMeshRoute, provenancePkg,
      coverCellPkg⟩

theorem FiniteLebesgueNumberCarrier_mesh_refinement_nonchoice [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow meshRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont mesh route meshRead ->
        PkgSig bundle meshRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row meshRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row radius ∨ hsame row mesh ∨ hsame row meshRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle meshRead pkg ∧
                  hsame row meshRead)
              hsame ∧
            UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory meshRead ∧
              Cont radius mesh route ∧ Cont mesh route meshRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle meshRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier meshRouteRead meshReadPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed meshUnary routeUnary meshRouteRead
  have sourceMeshRead :
      (fun row : BHist => hsame row meshRead ∧ UnaryHistory row) meshRead := by
    exact ⟨hsame_refl meshRead, meshReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row meshRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row mesh ∨ hsame row meshRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle meshRead pkg ∧
              hsame row meshRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro meshRead sourceMeshRead
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
      exact ⟨provenancePkg, meshReadPkg, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, meshUnary, meshReadUnary, radiusMeshRoute, meshRouteRead,
      provenancePkg, meshReadPkg⟩

theorem FiniteLebesgueNumberCarrier_compact_consumer_route [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        PkgSig bundle compactRead pkg ->
          UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
            UnaryHistory mesh ∧ UnaryHistory compactRead ∧ Cont cover window radius ∧
              Cont radius mesh compactRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompactRead compactReadPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompactRead
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, compactReadUnary, coverWindowRadius,
      radiusMeshCompactRead, provenancePkg, compactReadPkg⟩

theorem FiniteLebesgueNumberStreamRegularWindowOrder [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow windowRead coverCell
      orderedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius windowRead ->
        Cont windowRead mesh coverCell ->
          Cont coverCell route orderedRead ->
            PkgSig bundle orderedRead pkg ->
              UnaryHistory windowRead ∧ UnaryHistory coverCell ∧ UnaryHistory orderedRead ∧
                Cont window radius windowRead ∧ Cont windowRead mesh coverCell ∧
                  Cont coverCell route orderedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle orderedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRadiusRead readMeshCell cellRouteOrdered orderedPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed windowReadUnary meshUnary readMeshCell
  have orderedReadUnary : UnaryHistory orderedRead :=
    unary_cont_closed coverCellUnary routeUnary cellRouteOrdered
  exact
    ⟨windowReadUnary, coverCellUnary, orderedReadUnary, windowRadiusRead, readMeshCell,
      cellRouteOrdered, provenancePkg, orderedPkg⟩

theorem FiniteLebesgueNumberCarrier_total_bounded_handoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead route totalRead ->
          PkgSig bundle totalRead pkg ->
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory compactRead ∧ UnaryHistory totalRead ∧
                Cont cover window radius ∧ Cont radius mesh compactRead ∧
                  Cont compactRead route totalRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle totalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompactRead compactRouteTotal totalReadPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompactRead
  have totalReadUnary : UnaryHistory totalRead :=
    unary_cont_closed compactReadUnary routeUnary compactRouteTotal
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, compactReadUnary, totalReadUnary,
      coverWindowRadius, radiusMeshCompactRead, compactRouteTotal, provenancePkg,
      totalReadPkg⟩

theorem FiniteLebesgueNumberPhaseRealTerminalRadiusReadiness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead terminalRead
      consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
      UnaryHistory terminalRead ->
      Cont auditRead terminalRead consumerRow ->
      PkgSig bundle auditRead pkg ->
      PkgSig bundle consumerRow pkg ->
        UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
          UnaryHistory mesh ∧ UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
            UnaryHistory consumerRow ∧ Cont cover window radius ∧ Cont radius mesh route ∧
              Cont route nameRow auditRead ∧ Cont auditRead terminalRead consumerRow ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameAudit terminalUnary auditTerminalConsumer _auditPkg consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed auditUnary terminalUnary auditTerminalConsumer
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, terminalUnary,
      consumerUnary, coverWindowRadius, radiusMeshRoute, routeNameAudit,
      auditTerminalConsumer, provenancePkg, consumerPkg⟩

theorem FiniteLebesgueNumberCarrier_real_phase_source_exhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead realPhaseRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow auditRead ->
        Cont auditRead radius realPhaseRead ->
          PkgSig bundle realPhaseRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row realPhaseRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                    hsame row realPhaseRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle realPhaseRead pkg ∧
                    hsame row realPhaseRead)
                hsame ∧
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ UnaryHistory auditRead ∧ UnaryHistory realPhaseRead ∧
                  Cont cover window radius ∧ Cont radius mesh route ∧
                    Cont route nameRow auditRead ∧ Cont auditRead radius realPhaseRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realPhaseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameAudit auditRadiusReal realPhasePkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have realPhaseUnary : UnaryHistory realPhaseRead :=
    unary_cont_closed auditUnary radiusUnary auditRadiusReal
  have sourceReal :
      (fun row : BHist => hsame row realPhaseRead ∧ UnaryHistory row) realPhaseRead := by
    exact ⟨hsame_refl realPhaseRead, realPhaseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realPhaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row realPhaseRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle realPhaseRead pkg ∧
              hsame row realPhaseRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realPhaseRead sourceReal
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
      exact ⟨provenancePkg, realPhasePkg, source.left⟩
  }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, auditUnary, realPhaseUnary,
      coverWindowRadius, radiusMeshRoute, routeNameAudit, auditRadiusReal, provenancePkg,
      realPhasePkg⟩

theorem FiniteLebesgueNumberCarrier_root_radius_coherence [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow cover' window' radius' mesh'
      transport' route' provenance' nameRow' coherence : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      FiniteLebesgueNumberCarrier cover' window' radius' mesh' transport' route' provenance'
          nameRow' bundle pkg ->
        Cont route route' coherence ->
          PkgSig bundle coherence pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row coherence ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row route ∨ hsame row route' ∨ hsame row coherence)
                (fun row : BHist => PkgSig bundle coherence pkg ∧ hsame row coherence)
                hsame ∧
              UnaryHistory route ∧ UnaryHistory route' ∧ UnaryHistory coherence ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle provenance' pkg ∧
                  PkgSig bundle coherence pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier carrier' routeCoherence coherencePkg
  obtain ⟨_coverUnary, _windowUnary, _radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  obtain ⟨_coverUnary', _windowUnary', _radiusUnary', _meshUnary', _transportUnary',
    routeUnary', _provenanceUnary', _nameRowUnary', _coverWindowRadius',
    _radiusMeshRoute', _routeNameProvenance', provenancePkg'⟩ := carrier'
  have coherenceUnary : UnaryHistory coherence :=
    unary_cont_closed routeUnary routeUnary' routeCoherence
  have sourceCoherence :
      (fun row : BHist => hsame row coherence ∧ UnaryHistory row) coherence := by
    exact ⟨hsame_refl coherence, coherenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coherence ∧ UnaryHistory row)
          (fun row : BHist => hsame row route ∨ hsame row route' ∨ hsame row coherence)
          (fun row : BHist => PkgSig bundle coherence pkg ∧ hsame row coherence)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coherence sourceCoherence
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
      exact ⟨coherencePkg, source.left⟩
  }
  exact
    ⟨cert, routeUnary, routeUnary', coherenceUnary, provenancePkg, provenancePkg',
      coherencePkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
