import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceOrderCompletenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive CauchySequenceOrderCompletenessUp : Type where
  | mk
      (orderRow algebraRow regularRow streamRow dyadicRow realSealRow metricBoundaryRow
        transportRow replayRow provenance localCert : BHist) :
      CauchySequenceOrderCompletenessUp

def CauchySequenceOrderCompletenessCarrier [AskSetup] [PackageSetup]
    (orderRow algebraRow regularRow streamRow dyadicRow realSealRow metricBoundaryRow
      transportRow replayRow provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory orderRow ∧
    UnaryHistory algebraRow ∧
      UnaryHistory regularRow ∧
        UnaryHistory streamRow ∧
          UnaryHistory dyadicRow ∧
            UnaryHistory realSealRow ∧
              UnaryHistory metricBoundaryRow ∧
                UnaryHistory transportRow ∧
                  UnaryHistory replayRow ∧
                    UnaryHistory provenance ∧
                      UnaryHistory localCert ∧
                        Cont orderRow algebraRow transportRow ∧
                          Cont regularRow streamRow replayRow ∧
                            hsame replayRow provenance ∧
                              hsame metricBoundaryRow provenance ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg

theorem CauchySequenceOrderCompletenessNamecertObligations [AskSetup] [PackageSetup]
    {orderRow algebraRow regularRow streamRow dyadicRow realSealRow metricBoundaryRow
      transportRow replayRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceOrderCompletenessCarrier orderRow algebraRow regularRow streamRow dyadicRow
        realSealRow metricBoundaryRow transportRow replayRow provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              CauchySequenceOrderCompletenessCarrier orderRow algebraRow regularRow streamRow
                dyadicRow realSealRow metricBoundaryRow transportRow replayRow provenance
                localCert bundle pkg)
          (fun row : BHist =>
            hsame row orderRow ∨ hsame row algebraRow ∨ hsame row regularRow ∨
              hsame row streamRow ∨ hsame row dyadicRow ∨ hsame row realSealRow ∨
                hsame row metricBoundaryRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory orderRow ∧ UnaryHistory algebraRow ∧ UnaryHistory regularRow ∧
          UnaryHistory streamRow ∧ UnaryHistory dyadicRow ∧ UnaryHistory realSealRow ∧
            UnaryHistory metricBoundaryRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier
  have carrierPacket :
      CauchySequenceOrderCompletenessCarrier orderRow algebraRow regularRow streamRow dyadicRow
        realSealRow metricBoundaryRow transportRow replayRow provenance localCert bundle pkg :=
    carrier
  obtain ⟨orderUnary, algebraUnary, regularUnary, streamUnary, dyadicUnary, realSealUnary,
    metricBoundaryUnary, _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary,
    _transportRoute, _replayRoute, _sameReplayProvenance, sameMetricBoundaryProvenance,
    provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              CauchySequenceOrderCompletenessCarrier orderRow algebraRow regularRow streamRow
                dyadicRow realSealRow metricBoundaryRow transportRow replayRow provenance
                localCert bundle pkg)
          (fun row : BHist =>
            hsame row orderRow ∨ hsame row algebraRow ∨ hsame row regularRow ∨
              hsame row streamRow ∨ hsame row dyadicRow ∨ hsame row realSealRow ∨
                hsame row metricBoundaryRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | refl =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (hsame_symm sameMetricBoundaryProvenance))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, orderUnary, algebraUnary, regularUnary, streamUnary, dyadicUnary, realSealUnary,
      metricBoundaryUnary, provenancePkg⟩

end BEDC.Derived.CauchySequenceOrderCompletenessUp
