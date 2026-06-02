import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateLedgerPublicBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadic stream regseq realSeal candidateLedger publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction handoff
        dischargeSocket transport route provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal route candidateLedger →
        Cont candidateLedger dischargeSocket publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row candidateLedger ∨
                      hsame row dischargeSocket ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                    PkgSig bundle publicRead pkg ∧
                      Cont candidateLedger dischargeSocket publicRead)
                hsame ∧
              UnaryHistory candidateLedger ∧ UnaryHistory publicRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro ledger realSealRouteCandidate candidateDischargePublic publicPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealTransport, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionDischargeSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateLedger :=
    unary_cont_closed realSealUnary routeUnary realSealRouteCandidate
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed candidateUnary dischargeSocketUnary candidateDischargePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row candidateLedger ∨
                hsame row dischargeSocket ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
              PkgSig bundle publicRead pkg ∧
                Cont candidateLedger dischargeSocket publicRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, realSealPkg, publicPkg, candidateDischargePublic⟩
  }
  exact ⟨cert, candidateUnary, publicUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
