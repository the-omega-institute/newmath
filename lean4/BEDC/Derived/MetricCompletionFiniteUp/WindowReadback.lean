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

theorem MetricCompletionFiniteCarrier_stability_transport [AskSetup] [PackageSetup]
    {M B W E R S H C P N M' B' W' E' R' S' H' C' P' N' sourceRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFiniteCarrier M B W E R S H C P N bundle pkg →
      hsame M M' →
        hsame B B' →
          hsame W W' →
            hsame E E' →
              hsame R R' →
                hsame S S' →
                  hsame H H' →
                    hsame C C' →
                      hsame P P' →
                        hsame N N' →
                          Cont M' B' sourceRead →
                            Cont W' E' readback →
                              PkgSig bundle P' pkg →
                                PkgSig bundle N' pkg →
                                  MetricCompletionFiniteCarrier M' B' W' E' R' S' H' C' P' N'
                                      bundle pkg ∧
                                    UnaryHistory sourceRead ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier sameM sameB sameW sameE sameR sameS sameH sameC sameP sameN
    sourceRoute readbackRoute provenancePkg localNamePkg
  obtain ⟨metricUnary, basisUnary, windowUnary, embeddingUnary, readbackUnary,
    selectorUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary' : UnaryHistory M' :=
    unary_transport metricUnary sameM
  have basisUnary' : UnaryHistory B' :=
    unary_transport basisUnary sameB
  have windowUnary' : UnaryHistory W' :=
    unary_transport windowUnary sameW
  have embeddingUnary' : UnaryHistory E' :=
    unary_transport embeddingUnary sameE
  have readbackUnary' : UnaryHistory R' :=
    unary_transport readbackUnary sameR
  have selectorUnary' : UnaryHistory S' :=
    unary_transport selectorUnary sameS
  have transportUnary' : UnaryHistory H' :=
    unary_transport transportUnary sameH
  have replayUnary' : UnaryHistory C' :=
    unary_transport replayUnary sameC
  have provenanceUnary' : UnaryHistory P' :=
    unary_transport provenanceUnary sameP
  have localNameUnary' : UnaryHistory N' :=
    unary_transport localNameUnary sameN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed metricUnary' basisUnary' sourceRoute
  have readbackRouteUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary' embeddingUnary' readbackRoute
  exact
    ⟨⟨metricUnary', basisUnary', windowUnary', embeddingUnary', readbackUnary',
      selectorUnary', transportUnary', replayUnary', provenanceUnary', localNameUnary',
      provenancePkg, localNamePkg⟩, sourceUnary, readbackRouteUnary⟩

end BEDC.Derived.MetricCompletionFiniteUp
