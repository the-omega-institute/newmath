import BEDC.Derived.PackageMapBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PackageMapBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PackageMapBoundaryCarrier [AskSetup] [PackageSetup]
    (theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute transport replay
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  UnaryHistory theoremMap ∧
    UnaryHistory gapMap ∧
      UnaryHistory traditionMap ∧
        UnaryHistory scientificMap ∧
          UnaryHistory axisBoundary ∧
            UnaryHistory auditRoute ∧
              UnaryHistory transport ∧
                UnaryHistory replay ∧
                  UnaryHistory provenance ∧
                    UnaryHistory nameCert ∧
                      Cont theoremMap gapMap traditionMap ∧
                        Cont traditionMap scientificMap axisBoundary ∧
                          Cont axisBoundary auditRoute transport ∧
                            Cont transport replay nameCert ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle nameCert pkg

theorem PackageMapBoundaryNameCertObligations [AskSetup] [PackageSetup]
    {theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute transport replay
      provenance nameCert auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PackageMapBoundaryCarrier theoremMap gapMap traditionMap scientificMap axisBoundary
        auditRoute transport replay provenance nameCert bundle pkg →
      Cont auditRoute nameCert auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row theoremMap ∨ hsame row gapMap ∨ hsame row traditionMap ∨
                  hsame row scientificMap ∨ hsame row axisBoundary ∨ hsame row auditRoute ∨
                    hsame row auditRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier auditRouteName auditPkg
  obtain ⟨_theoremUnary, _gapUnary, traditionUnary, scientificUnary, axisUnary,
    auditRouteUnary, _transportUnary, _replayUnary, provenanceUnary, nameCertUnary,
    _theoremGapTradition, traditionScientificAxis, _axisAuditTransport,
    _transportReplayName, provenancePkg, _namePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditRouteUnary nameCertUnary auditRouteName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row theoremMap ∨ hsame row gapMap ∨ hsame row traditionMap ∨
              hsame row scientificMap ∨ hsame row axisBoundary ∨ hsame row auditRoute ∨
                hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditReadUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditPkg, provenancePkg⟩
  }
  exact ⟨cert, auditReadUnary⟩

end BEDC.Derived.PackageMapBoundaryUp
