import BEDC.Derived.MetricCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricCompletionCarrier [AskSetup] [PackageSetup]
    (source filterBranch netBranch readback separated transport replay provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory source ∧ UnaryHistory filterBranch ∧ UnaryHistory netBranch ∧
    UnaryHistory readback ∧ UnaryHistory separated ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont readback separated replay ∧ hsame transport provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg

theorem MetricCompletionCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              MetricCompletionCarrier source filterBranch netBranch readback separated transport
                replay provenance localCert bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory readback ∧ Cont readback separated replay ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  have carrierPacket :
      MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _filterUnary, _netUnary, readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, replayRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              MetricCompletionCarrier source filterBranch netBranch readback separated transport
                replay provenance localCert bundle pkg)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierPacket⟩
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
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow.left
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg⟩
    }
  exact ⟨cert, sourceUnary, readbackUnary, replayRoute, provenancePkg⟩

end BEDC.Derived.MetricCompletionUp.NameCertObligations
