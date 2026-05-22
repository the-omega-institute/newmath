import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyRealOrderCarrier [AskSetup] [PackageSetup]
    (sourceLeft sourceRight window dyadic quotient realSeal verdict transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  UnaryHistory sourceLeft ∧ UnaryHistory sourceRight ∧ UnaryHistory window ∧
    UnaryHistory dyadic ∧ UnaryHistory quotient ∧ UnaryHistory realSeal ∧
      UnaryHistory verdict ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧
          Cont sourceLeft sourceRight window ∧ Cont window dyadic quotient ∧
            Cont quotient realSeal verdict ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg

theorem CauchyRealOrderCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceLeft sourceRight window dyadic quotient realSeal verdict transport replay provenance
      nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealOrderCarrier sourceLeft sourceRight window dyadic quotient realSeal verdict
        transport replay provenance nameRow bundle pkg ->
      Cont replay nameRow auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceLeft ∨ hsame row sourceRight ∨ hsame row window ∨
                  hsame row dyadic ∨ hsame row quotient ∨ hsame row realSeal ∨
                    hsame row verdict ∨ hsame row auditRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                  hsame row auditRead)
              hsame ∧
            UnaryHistory sourceLeft ∧ UnaryHistory sourceRight ∧ UnaryHistory window ∧
              UnaryHistory dyadic ∧ UnaryHistory quotient ∧ UnaryHistory realSeal ∧
                UnaryHistory verdict ∧ UnaryHistory auditRead ∧
                  Cont replay nameRow auditRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier replayNameAudit auditPkg
  obtain ⟨sourceLeftUnary, sourceRightUnary, windowUnary, dyadicUnary, quotientUnary,
    realSealUnary, verdictUnary, _transportUnary, replayUnary, _provenanceUnary,
    nameRowUnary, _sourcePairWindow, _windowDyadicQuotient, _quotientRealVerdict,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary nameRowUnary replayNameAudit
  have sourceAudit :
      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row) auditRead := by
    exact ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceLeft ∨ hsame row sourceRight ∨ hsame row window ∨
              hsame row dyadic ∨ hsame row quotient ∨ hsame row realSeal ∨
                hsame row verdict ∨ hsame row auditRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              hsame row auditRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro auditRead sourceAudit
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditPkg, source.left⟩
    }
  exact
    ⟨cert, sourceLeftUnary, sourceRightUnary, windowUnary, dyadicUnary, quotientUnary,
      realSealUnary, verdictUnary, auditUnary, replayNameAudit, provenancePkg, auditPkg⟩

end BEDC.Derived.CauchyRealOrderUp
