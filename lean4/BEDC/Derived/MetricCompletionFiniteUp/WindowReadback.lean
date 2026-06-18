import BEDC.Derived.MetricCompletionFiniteUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletionFiniteWindowReadback [AskSetup] [PackageSetup]
    {M B W E R S H C P N finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFiniteCarrier M B W E R S H C P N bundle pkg →
      Cont M B W →
        Cont W E S →
          Cont S R finalRead →
            PkgSig bundle finalRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row B ∨ hsame row W ∨ hsame row E ∨
                      hsame row S ∨ hsame row R ∨ hsame row finalRead)
                  (fun row : BHist => hsame row finalRead ∧ PkgSig bundle finalRead pkg)
                  hsame ∧
                UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory E ∧
                  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory finalRead ∧
                    Cont M B W ∧ Cont W E S ∧ Cont S R finalRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert UnaryHistory
  intro carrier metricBasisRoute windowEmbeddingRoute selectorReadRoute finalReadPkg
  obtain ⟨metricUnary, basisUnary, windowUnary, embeddingUnary, readbackUnary,
    selectorUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed selectorUnary readbackUnary selectorReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row B ∨ hsame row W ∨ hsame row E ∨
              hsame row S ∨ hsame row R ∨ hsame row finalRead)
          (fun row : BHist => hsame row finalRead ∧ PkgSig bundle finalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead (And.intro (hsame_refl finalRead) finalReadUnary)
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
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left finalReadPkg
  }
  exact
    ⟨cert, metricUnary, basisUnary, windowUnary, embeddingUnary, selectorUnary,
      readbackUnary, finalReadUnary, metricBasisRoute, windowEmbeddingRoute, selectorReadRoute,
      provenancePkg, finalReadPkg⟩

end BEDC.Derived.MetricCompletionFiniteUp
