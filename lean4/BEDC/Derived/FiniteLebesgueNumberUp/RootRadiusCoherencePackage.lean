import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRealCompletionRadiusNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead terminalRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius terminalRead →
          Cont terminalRead provenance completionRead →
            PkgSig bundle auditRead pkg →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row radius ∨ hsame row terminalRead ∨ hsame row completionRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                        hsame row completionRead)
                    hsame ∧
                  UnaryHistory radius ∧ UnaryHistory auditRead ∧ UnaryHistory terminalRead ∧
                    UnaryHistory completionRead ∧ Cont route nameRow auditRead ∧
                      Cont auditRead radius terminalRead ∧
                        Cont terminalRead provenance completionRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameAudit auditRadiusTerminal terminalProvenanceCompletion _auditPkg
    completionPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary radiusUnary auditRadiusTerminal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed terminalUnary provenanceUnary terminalProvenanceCompletion
  have completionCarrier :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row radius ∨ hsame row terminalRead ∨ hsame row completionRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
            hsame row completionRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead completionCarrier
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
        exact ⟨provenancePkg, completionPkg, source.left⟩
    }
  exact
    ⟨cert, radiusUnary, auditUnary, terminalUnary, completionUnary, routeNameAudit,
      auditRadiusTerminal, terminalProvenanceCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
