import BEDC.Derived.LogicContradictionMetaLoopUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LogicContradictionMetaLoopUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LogicContradictionMetaLoopCarrierAdmission [AskSetup] [PackageSetup]
    {proofPattern refutation metaRefusal auditGate transport replay provenance localName
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LogicContradictionMetaLoopCarrier proofPattern refutation metaRefusal auditGate
        transport replay provenance localName bundle pkg →
      Cont provenance localName namedRead →
        logicContradictionMetaLoopFields
            (LogicContradictionMetaLoopUp.mk proofPattern refutation metaRefusal auditGate
              transport replay provenance localName) =
            [proofPattern, refutation, metaRefusal, auditGate, transport, replay,
              provenance, localName] ∧
          SemanticNameCert
              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row proofPattern ∨ hsame row refutation ∨ hsame row metaRefusal ∨
                  hsame row auditGate ∨ hsame row transport ∨ hsame row replay ∨
                    hsame row provenance ∨ hsame row localName ∨ hsame row namedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont proofPattern refutation metaRefusal ∧
                  Cont metaRefusal auditGate replay ∧ Cont transport replay provenance ∧
                    Cont provenance localName namedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory metaRefusal ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier nameRoute
  obtain ⟨proofPatternUnary, refutationUnary, auditGateUnary, transportUnary, localNameUnary,
    proofRefutationMeta, metaAuditReplay, transportReplayProvenance, provenancePkg,
    localNamePkg⟩ := carrier
  have metaRefusalUnary : UnaryHistory metaRefusal :=
    unary_cont_closed proofPatternUnary refutationUnary proofRefutationMeta
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed metaRefusalUnary auditGateUnary metaAuditReplay
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary localNameUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row proofPattern ∨ hsame row refutation ∨ hsame row metaRefusal ∨
              hsame row auditGate ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont proofPattern refutation metaRefusal ∧
              Cont metaRefusal auditGate replay ∧ Cont transport replay provenance ∧
                Cont provenance localName namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, proofRefutationMeta, metaAuditReplay, transportReplayProvenance,
            nameRoute, provenancePkg, localNamePkg⟩
    }
  exact
    ⟨rfl, cert, metaRefusalUnary, replayUnary, provenanceUnary, namedUnary⟩

end BEDC.Derived.LogicContradictionMetaLoopUp
