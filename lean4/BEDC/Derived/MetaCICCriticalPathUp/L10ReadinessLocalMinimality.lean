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

theorem MetaCICCriticalPathL10ReadinessLocalMinimality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal readiness localSupport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont dyadic stream readiness ->
        Cont readiness localName localSupport ->
          PkgSig bundle localSupport pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row localSupport ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row readiness ∨ hsame row localSupport)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont dyadic stream readiness ∧
                    Cont readiness localName localSupport ∧
                      PkgSig bundle localSupport pkg ∧ PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory readiness ∧ UnaryHistory localSupport ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger readinessRoute localSupportRoute localSupportPkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed dyadicUnary streamUnary readinessRoute
  have localSupportUnary : UnaryHistory localSupport :=
    unary_cont_closed readinessUnary localNameUnary localSupportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localSupport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row readiness ∨ hsame row localSupport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream readiness ∧
              Cont readiness localName localSupport ∧ PkgSig bundle localSupport pkg ∧
                PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localSupport ⟨hsame_refl localSupport, localSupportUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, readinessRoute, localSupportRoute, localSupportPkg, realSealPkg⟩
  }
  exact ⟨cert, readinessUnary, localSupportUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
