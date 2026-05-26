import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootOutputConsumerDownstreamCoverage
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert rootRead coverage : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont audit boundary rootRead →
        PkgSig bundle rootRead pkg →
          hsame coverage rootRead →
            SemanticNameCert
                (fun row : BHist => hsame row coverage ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row signature ∨ hsame row branch ∨ hsame row descent ∨
                    hsame row output ∨ hsame row coverage)
                (fun row : BHist => hsame row coverage ∧ PkgSig bundle rootRead pkg)
                hsame ∧
              UnaryHistory coverage ∧ Cont audit boundary rootRead ∧
                PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier auditBoundary rootPkg coverageRoot
  rcases carrier with
    ⟨signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _sameTransport, _provenancePkg⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed auditUnary boundaryUnary auditBoundary
  have coverageUnary : UnaryHistory coverage :=
    unary_transport rootUnary (hsame_symm coverageRoot)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverage ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature ∨ hsame row branch ∨ hsame row descent ∨
              hsame row output ∨ hsame row coverage)
          (fun row : BHist => hsame row coverage ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro coverage ⟨hsame_refl coverage, coverageUnary⟩
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
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rootPkg⟩
  }
  exact ⟨cert, coverageUnary, auditBoundary, rootPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
