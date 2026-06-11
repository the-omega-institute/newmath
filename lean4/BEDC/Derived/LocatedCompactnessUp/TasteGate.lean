import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCompactnessCarrier [AskSetup] [PackageSetup]
    (metric compact closedBall localSupport radius stream transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory metric ∧ UnaryHistory compact ∧ UnaryHistory closedBall ∧
    UnaryHistory localSupport ∧ UnaryHistory radius ∧ UnaryHistory stream ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont metric compact closedBall ∧
          Cont closedBall localSupport radius ∧ Cont radius stream replay ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem LocatedCompactnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric compact closedBall localSupport radius stream transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCompactnessCarrier metric compact closedBall localSupport radius stream transport replay
        provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            LocatedCompactnessCarrier metric compact closedBall localSupport radius stream
              transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            LocatedCompactnessCarrier metric compact closedBall localSupport radius stream
              transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: LocatedCompactnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierSource := carrier
  obtain ⟨_metricUnary, _compactUnary, _closedBallUnary, _localSupportUnary, _radiusUnary,
    _streamUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _metricCompactClosedBall, _closedBallSupportRadius, _radiusStreamReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport localNameUnary (hsame_symm source.right), localNamePkg⟩
  }

end BEDC.Derived.LocatedCompactnessUp
