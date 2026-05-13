import BEDC.Derived.SubjectReductionDischargeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionDischargeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionDischargeCarrier [AskSetup] [PackageSetup]
    (beta appArg lamDomain piDomain compilerBoundary kernelRoutes obstruction transports
      routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
    UnaryHistory piDomain ∧ UnaryHistory compilerBoundary ∧ UnaryHistory kernelRoutes ∧
      UnaryHistory obstruction ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧
          Cont compilerBoundary kernelRoutes transports ∧
            Cont transports routes provenance ∧ PkgSig bundle provenance pkg

theorem SubjectReductionDischargeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {beta appArg lamDomain piDomain compilerBoundary kernelRoutes obstruction transports routes
      provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeCarrier beta appArg lamDomain piDomain compilerBoundary
        kernelRoutes obstruction transports routes provenance nameRow bundle pkg ->
      Cont routes nameRow auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row nameRow ∧
                  SubjectReductionDischargeCarrier beta appArg lamDomain piDomain
                    compilerBoundary kernelRoutes obstruction transports routes provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row nameRow)
              (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
              UnaryHistory piDomain ∧ UnaryHistory obstruction ∧ UnaryHistory auditRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier auditRoute auditPkg
  have carrierPacket := carrier
  obtain ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, _compilerBoundaryUnary,
    _kernelRoutesUnary, obstructionUnary, _transportsUnary, routesUnary, _provenanceUnary,
    nameRowUnary, _compilerTransport, _transportProvenance, provenancePkg⟩ := carrierPacket
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed routesUnary nameRowUnary auditRoute
  have sourceAtName :
      (fun row : BHist =>
        hsame row nameRow ∧
          SubjectReductionDischargeCarrier beta appArg lamDomain piDomain compilerBoundary
            kernelRoutes obstruction transports routes provenance nameRow bundle pkg)
          nameRow :=
    And.intro (hsame_refl nameRow) carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row nameRow ∧
            SubjectReductionDischargeCarrier beta appArg lamDomain piDomain compilerBoundary
              kernelRoutes obstruction transports routes provenance nameRow bundle pkg)
        (fun row : BHist => hsame row nameRow)
        (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRow sourceAtName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    And.intro cert
      (And.intro betaUnary
        (And.intro appArgUnary
          (And.intro lamDomainUnary
            (And.intro piDomainUnary
              (And.intro obstructionUnary
                (And.intro auditReadUnary
                  (And.intro provenancePkg auditPkg)))))))

end BEDC.Derived.SubjectReductionDischargeUp
