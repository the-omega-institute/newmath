import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp.ScopePackage

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_namecert_scope_package [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont localName provenance scopeRead →
        PkgSig bundle scopeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                  hsame row target ∨ hsame row transport ∨ hsame row replay ∨
                    hsame row localName ∨ hsame row scopeRead)
              (fun row : BHist =>
                hsame row scopeRead ∧ PkgSig bundle scopeRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory scopeRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier localNameProvenanceRead scopeReadPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, _targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed localNameUnary provenanceUnary localNameProvenanceRead
  have sourceScopeRead :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead := by
    exact ⟨hsame_refl scopeRead, scopeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row transport ∨ hsame row replay ∨
                hsame row localName ∨ hsame row scopeRead)
          (fun row : BHist =>
            hsame row scopeRead ∧ PkgSig bundle scopeRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScopeRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, scopeReadPkg, provenancePkg⟩
  }
  exact ⟨cert, scopeReadUnary, provenancePkg⟩

theorem RepresentedSpaceCarrier_scoped_package [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scopeRead metricRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg →
      Cont localName provenance scopeRead →
        Cont target transport metricRead →
          Cont metricRead localName completionRead →
            PkgSig bundle scopeRead pkg →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                        hsame row target ∨ hsame row transport ∨ hsame row replay ∨
                          hsame row localName ∨ hsame row scopeRead ∨
                            hsame row completionRead)
                    (fun row : BHist =>
                      hsame row scopeRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle scopeRead pkg ∧ PkgSig bundle completionRead pkg)
                    hsame ∧
                  UnaryHistory scopeRead ∧ UnaryHistory metricRead ∧
                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier localNameProvenanceRead targetTransportMetric metricLocalCompletion
    scopeReadPkg completionReadPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, transportUnary,
    replayUnary, provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed localNameUnary provenanceUnary localNameProvenanceRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed targetUnary transportUnary targetTransportMetric
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary localNameUnary metricLocalCompletion
  have sourceScopeRead :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead := by
    exact ⟨hsame_refl scopeRead, scopeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row transport ∨ hsame row replay ∨ hsame row localName ∨
                hsame row scopeRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row scopeRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle scopeRead pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScopeRead
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, scopeReadPkg, completionReadPkg⟩
  }
  have _carrierRows :
      UnaryHistory name ∧ UnaryHistory schedule ∧ UnaryHistory relation ∧ UnaryHistory replay :=
    ⟨nameUnary, scheduleUnary, relationUnary, replayUnary⟩
  exact ⟨cert, scopeReadUnary, metricReadUnary, completionReadUnary⟩

end BEDC.Derived.RepresentedSpaceUp.ScopePackage
