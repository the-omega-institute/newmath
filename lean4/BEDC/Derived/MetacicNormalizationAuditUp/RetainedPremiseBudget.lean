import BEDC.Derived.MetacicNormalizationAuditUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditRetainedPremiseBudget [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      candidateRead closedRead spentFuel retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont frontier sn candidateRead →
        Cont candidateRead audit closedRead →
          Cont closedRead replay spentFuel →
            Cont spentFuel localName retainedRead →
              PkgSig bundle retainedRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row retainedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist =>
                      hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                        hsame row candidateRead ∨ hsame row closedRead ∨
                          hsame row replay ∨ hsame row spentFuel ∨ hsame row localName ∨
                            hsame row retainedRead ∨ hsame row provenance)
                    (fun row : BHist =>
                      hsame row retainedRead ∧ Cont frontier sn candidateRead ∧
                        Cont candidateRead audit closedRead ∧ Cont closedRead replay spentFuel ∧
                          Cont spentFuel localName retainedRead ∧
                            PkgSig bundle provenance pkg)
                    hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory closedRead ∧
                  UnaryHistory spentFuel ∧ UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnCandidate candidateAuditClosed closedReplaySpent
    spentLocalRetained retainedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary auditUnary candidateAuditClosed
  have spentUnary : UnaryHistory spentFuel :=
    unary_cont_closed closedUnary replayUnary closedReplaySpent
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed spentUnary localNameUnary spentLocalRetained
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row retainedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row candidateRead ∨ hsame row closedRead ∨ hsame row replay ∨
                hsame row spentFuel ∨ hsame row localName ∨ hsame row retainedRead ∨
                  hsame row provenance)
          (fun row : BHist =>
            hsame row retainedRead ∧ Cont frontier sn candidateRead ∧
              Cont candidateRead audit closedRead ∧ Cont closedRead replay spentFuel ∧
                Cont spentFuel localName retainedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro retainedRead ⟨hsame_refl retainedRead, retainedUnary, retainedPkg⟩
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
        intro _row other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, frontierSnCandidate, candidateAuditClosed, closedReplaySpent,
          spentLocalRetained, provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, closedUnary, spentUnary, retainedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
