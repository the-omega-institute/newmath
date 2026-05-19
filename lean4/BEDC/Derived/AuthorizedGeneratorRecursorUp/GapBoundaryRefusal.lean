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

theorem AuthorizedGeneratorRecursorGapBoundaryRefusal [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert refused gate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont boundary localCert refused ->
        Cont refused audit gate ->
          PkgSig bundle gate pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row gate ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont boundary localCert refused ∧ Cont refused audit row ∧ hsame row gate)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle gate pkg ∧ hsame row gate)
                hsame ∧
              UnaryHistory boundary ∧ UnaryHistory localCert ∧ UnaryHistory refused ∧
                UnaryHistory gate := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier boundaryLocalRefused refusedAuditGate gatePkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    _outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportSameAuditContinuation, provenancePkg⟩ := carrier
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed boundaryUnary localCertUnary boundaryLocalRefused
  have gateUnary : UnaryHistory gate :=
    unary_cont_closed refusedUnary auditUnary refusedAuditGate
  have sourceRefused :
      (fun row : BHist => hsame row gate ∧ UnaryHistory row) gate := by
    exact ⟨hsame_refl gate, gateUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row gate ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont boundary localCert refused ∧ Cont refused audit row ∧ hsame row gate)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle gate pkg ∧ hsame row gate)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro gate sourceRefused
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact
        ⟨boundaryLocalRefused,
          cont_result_hsame_transport refusedAuditGate (hsame_symm source.left),
          source.left⟩
    ledger_sound := by
      intro row source
      exact ⟨provenancePkg, gatePkg, source.left⟩
  }
  exact ⟨cert, boundaryUnary, localCertUnary, refusedUnary, gateUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
