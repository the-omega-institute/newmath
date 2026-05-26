import BEDC.Derived.FormalBallCompletionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric radius dyadic window transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier metric radius dyadic window transport replay provenance localName
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              FormalBallCarrier metric radius dyadic window transport replay provenance
                localName bundle pkg)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric radius dyadic ∧ Cont dyadic window replay)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory metric ∧ UnaryHistory radius ∧ UnaryHistory dyadic ∧
          UnaryHistory window ∧ Cont metric radius dyadic ∧ Cont dyadic window replay ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource :
      FormalBallCarrier metric radius dyadic window transport replay provenance localName
        bundle pkg := carrier
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, metricRadiusDyadic,
    dyadicWindowReplay, _transportReplayProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              FormalBallCarrier metric radius dyadic window transport replay provenance
                localName bundle pkg)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric radius dyadic ∧ Cont dyadic window replay)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName
          ⟨hsame_refl localName, carrierSource⟩
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
        exact ⟨source.left, metricRadiusDyadic, dyadicWindowReplay⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, metricUnary, radiusUnary, dyadicUnary, windowUnary, metricRadiusDyadic,
      dyadicWindowReplay, provenancePkg⟩

end BEDC.Derived.FormalBallUp
