import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealPrefixDiagnosticCarrier [AskSetup] [PackageSetup]
    (prefixRow window stream readback dyadic realSeal answer transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory prefixRow ∧ UnaryHistory window ∧ UnaryHistory stream ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
      UnaryHistory answer ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont prefixRow window stream ∧
          Cont stream readback dyadic ∧ Cont dyadic realSeal answer ∧
            hsame localName answer ∧ PkgSig bundle provenance pkg

namespace RealPrefixDiagnosticUp

theorem RealPrefixDiagnosticCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {prefixRow window stream readback dyadic realSeal answer transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPrefixDiagnosticCarrier prefixRow window stream readback dyadic realSeal answer
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              RealPrefixDiagnosticCarrier prefixRow window stream readback dyadic realSeal answer
                transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row prefixRow ∨ hsame row window ∨ hsame row stream ∨ hsame row readback ∨
              hsame row dyadic ∨ hsame row realSeal ∨ hsame row answer)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory prefixRow ∧ UnaryHistory window ∧ UnaryHistory stream ∧
          UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
            UnaryHistory answer ∧ Cont prefixRow window stream ∧ Cont stream readback dyadic ∧
              Cont dyadic realSeal answer ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness :
      RealPrefixDiagnosticCarrier prefixRow window stream readback dyadic realSeal answer
        transport replay provenance localName bundle pkg :=
    carrier
  obtain ⟨prefixUnary, windowUnary, streamUnary, readbackUnary, dyadicUnary,
    realSealUnary, answerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, prefixWindowStream, streamReadbackDyadic, dyadicRealSealAnswer,
    localNameAnswer, provenancePkg⟩ := carrier
  have sourceLocalName :
      (fun row : BHist =>
        hsame row localName ∧
          RealPrefixDiagnosticCarrier prefixRow window stream readback dyadic realSeal answer
            transport replay provenance localName bundle pkg) localName := by
    exact ⟨hsame_refl localName, carrierWitness⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              RealPrefixDiagnosticCarrier prefixRow window stream readback dyadic realSeal answer
                transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row prefixRow ∨ hsame row window ∨ hsame row stream ∨ hsame row readback ∨
              hsame row dyadic ∨ hsame row realSeal ∨ hsame row answer)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (hsame_trans source.left localNameAnswer))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, prefixUnary, windowUnary, streamUnary, readbackUnary, dyadicUnary, realSealUnary,
      answerUnary, prefixWindowStream, streamReadbackDyadic, dyadicRealSealAnswer,
      provenancePkg⟩

end RealPrefixDiagnosticUp

end BEDC.Derived
