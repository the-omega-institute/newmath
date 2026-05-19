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

end BEDC.Derived.FiniteLebesgueNumberUp
