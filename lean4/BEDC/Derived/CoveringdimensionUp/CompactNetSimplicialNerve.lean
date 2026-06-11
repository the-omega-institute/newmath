import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetSimplicialNerve [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName netRoot nerve : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet netRoot →
        Cont netRoot refinement nerve →
          PkgSig bundle nerve pkg →
            SemanticNameCert
                (fun row : BHist => hsame row nerve ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row netRoot ∨
                    hsame row refinement ∨ hsame row nerve)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet netRoot ∧
                    Cont netRoot refinement nerve ∧ PkgSig bundle nerve pkg)
                hsame ∧
              UnaryHistory netRoot ∧ UnaryHistory nerve := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactNetRoot netRootRefinementNerve nervePkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have netRootUnary : UnaryHistory netRoot :=
    unary_cont_closed compactUnary epsilonUnary compactNetRoot
  have nerveUnary : UnaryHistory nerve :=
    unary_cont_closed netRootUnary refinementUnary netRootRefinementNerve
  have sourceNerve :
      (fun row : BHist => hsame row nerve ∧ UnaryHistory row) nerve := by
    exact ⟨hsame_refl nerve, nerveUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nerve ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row netRoot ∨
              hsame row refinement ∨ hsame row nerve)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet netRoot ∧
              Cont netRoot refinement nerve ∧ PkgSig bundle nerve pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nerve sourceNerve
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactNetRoot, netRootRefinementNerve, nervePkg⟩
  }
  exact ⟨cert, netRootUnary, nerveUnary⟩

end BEDC.Derived.CoveringdimensionUp
