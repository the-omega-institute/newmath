import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CatZeroMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CatZeroMetricCarrier [AskSetup] [PackageSetup]
    (M G V E A Q D L H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory Q ∧
    Cont M G V ∧ Cont A Q D ∧ Cont Q D L ∧ Cont E L H ∧ Cont H C P ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CatZeroMetricCarrier_comparison_obligations [AskSetup] [PackageSetup]
    {M G V E A Q D L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row Q ∧ CatZeroMetricCarrier M G V E A Q D L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row V ∨ hsame row E ∨
              hsame row A ∨ hsame row Q ∨ hsame row D ∨ hsame row L ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory Q ∧ Cont M G V ∧
          Cont A Q D := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier
  rcases carrier with
    ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
      alexandrovComparisonDomain, comparisonDomainHandoff, edgeHandoffTransport,
      transportContinuationProvenance, provenancePkg, localNamePkg⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro Q
            ⟨hsame_refl Q,
              ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
                alexandrovComparisonDomain, comparisonDomainHandoff, edgeHandoffTransport,
                transportContinuationProvenance, provenancePkg, localNamePkg⟩⟩
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
            ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl source.left)))))
      ledger_sound := by
        intro row source
        exact
          ⟨unary_transport comparisonUnary (hsame_symm source.left), provenancePkg,
            localNamePkg⟩
    }
  · exact
      ⟨metricUnary, geodesicUnary, comparisonUnary, metricGeodesicVertex,
        alexandrovComparisonDomain⟩

end BEDC.Derived.CatZeroMetricUp
