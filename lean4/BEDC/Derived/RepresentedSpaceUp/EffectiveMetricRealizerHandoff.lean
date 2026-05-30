import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_effective_metric_realizer_handoff [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName streamRead relationRead
      targetRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg →
      Cont name schedule streamRead →
        Cont streamRead relation relationRead →
          Cont target localName targetRead →
            Cont relationRead targetRead metricRead →
              PkgSig bundle streamRead pkg →
                PkgSig bundle metricRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row streamRead ∨ hsame row metricRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                          hsame row target ∨ hsame row streamRead ∨ hsame row relationRead ∨
                            hsame row targetRead ∨ hsame row metricRead)
                      (fun row : BHist =>
                        (hsame row streamRead ∨ hsame row metricRead) ∧
                          PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory streamRead ∧ UnaryHistory relationRead ∧
                      UnaryHistory targetRead ∧ UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleStream streamRelationRead targetLocalNameRead
    relationTargetMetricRead streamReadPkg metricReadPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleStream
  have relationReadUnary : UnaryHistory relationRead :=
    unary_cont_closed streamReadUnary relationUnary streamRelationRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed relationReadUnary targetReadUnary relationTargetMetricRead
  have sourceStreamRead :
      (fun row : BHist =>
        (hsame row streamRead ∨ hsame row metricRead) ∧ UnaryHistory row) streamRead := by
    exact ⟨Or.inl (hsame_refl streamRead), streamReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row streamRead ∨ hsame row metricRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row streamRead ∨ hsame row relationRead ∨
                hsame row targetRead ∨ hsame row metricRead)
          (fun row : BHist =>
            (hsame row streamRead ∨ hsame row metricRead) ∧
              PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro streamRead sourceStreamRead
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
        cases source.left with
        | inl sameStream =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameStream),
                unary_transport source.right sameRows⟩
        | inr sameMetric =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameMetric),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameStream =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
      | inr sameMetric =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameMetric))))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameStream =>
          cases sameStream
          exact ⟨Or.inl (hsame_refl streamRead), streamReadPkg, provenancePkg⟩
      | inr sameMetric =>
          cases sameMetric
          exact ⟨Or.inr (hsame_refl metricRead), metricReadPkg, provenancePkg⟩
  }
  exact
    ⟨cert, streamReadUnary, relationReadUnary, targetReadUnary, metricReadUnary⟩

end BEDC.Derived.RepresentedSpaceUp
