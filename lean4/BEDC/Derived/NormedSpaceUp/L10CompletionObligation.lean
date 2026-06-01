import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_l10_completion_obligation [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead replayRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont completionRead T replayRead ->
              Cont replayRead C l10Read ->
                PkgSig bundle l10Read pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                          hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
                            hsame row l10Read)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle l10Read pkg ∧ Cont metricRead Q completionRead)
                      hsame ∧
                    UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory replayRead ∧
                        UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier normRoute metricRoute completionRoute replayRoute l10Route l10Pkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, _hUnary, tUnary, provenanceUnary,
    cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed completionReadUnary tUnary replayRoute
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed replayReadUnary cUnary l10Route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row C ∨
                hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧
              PkgSig bundle l10Read pkg ∧ Cont metricRead Q completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro l10Read ⟨hsame_refl l10Read, l10ReadUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, l10Pkg, completionRoute⟩
  }
  exact
    ⟨cert, normReadUnary, metricReadUnary, completionReadUnary, replayReadUnary,
      l10ReadUnary⟩

end BEDC.Derived.NormedSpaceUp
