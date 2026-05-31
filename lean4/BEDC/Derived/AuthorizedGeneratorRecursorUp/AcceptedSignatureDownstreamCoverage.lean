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

theorem AuthorizedGeneratorRecursorAcceptedSignatureDownstreamCoverage
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert admission outputRead coverage : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont signature branch admission →
        Cont admission output outputRead →
          PkgSig bundle outputRead pkg →
            hsame coverage outputRead →
              SemanticNameCert
                  (fun row : BHist => hsame row coverage ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row signature ∨ hsame row branch ∨ hsame row descent ∨
                      hsame row output ∨ hsame row coverage)
                  (fun row : BHist => hsame row coverage ∧ PkgSig bundle outputRead pkg)
                  hsame ∧
                UnaryHistory coverage ∧ Cont signature branch admission ∧
                  Cont admission output outputRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier signatureBranch admissionOutput outputPkg coverageOutput
  rcases carrier with
    ⟨signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
      outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _sameTransport, _provenancePkg⟩
  have admissionUnary : UnaryHistory admission :=
    unary_cont_closed signatureUnary branchUnary signatureBranch
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed admissionUnary outputUnary admissionOutput
  have coverageUnary : UnaryHistory coverage :=
    unary_transport outputReadUnary (hsame_symm coverageOutput)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverage ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature ∨ hsame row branch ∨ hsame row descent ∨
              hsame row output ∨ hsame row coverage)
          (fun row : BHist => hsame row coverage ∧ PkgSig bundle outputRead pkg)
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
      exact ⟨source.left, outputPkg⟩
  }
  exact ⟨cert, coverageUnary, signatureBranch, admissionOutput⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
