import BEDC.Derived.CompleteSeparableMetricUp.DensityCompletionHandoff

namespace BEDC.Derived.CompleteSeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompleteSeparableMetricCarrier_finite_window_density_seal [AskSetup] [PackageSetup]
    {M K D W T R E H C P N metricDense denseWindow toleranceRead regularRead sealRead
      boundaryRead replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompleteSeparableMetricCarrier M K D W T R E H C P N bundle pkg ->
      Cont M D metricDense ->
        Cont metricDense W denseWindow ->
          Cont denseWindow T toleranceRead ->
            Cont toleranceRead R regularRead ->
              Cont regularRead K sealRead ->
                Cont sealRead E boundaryRead ->
                  Cont boundaryRead H replayRead ->
                    Cont replayRead C publicRead ->
                      PkgSig bundle publicRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row M ∨ hsame row D ∨ hsame row W ∨ hsame row T ∨
                                hsame row R ∨ hsame row K ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory metricDense ∧ UnaryHistory denseWindow ∧
                            UnaryHistory toleranceRead ∧ UnaryHistory regularRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory boundaryRead ∧
                                UnaryHistory replayRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricDenseRoute denseWindowRoute toleranceRoute regularRoute sealRoute
    boundaryRoute replayRoute publicRoute publicPkg
  obtain ⟨mUnary, kUnary, dUnary, wUnary, tUnary, rUnary, eUnary, hUnary, cUnary,
    _pUnary, _nUnary, _nPkg⟩ := carrier
  have metricDenseUnary : UnaryHistory metricDense :=
    unary_cont_closed mUnary dUnary metricDenseRoute
  have denseWindowUnary : UnaryHistory denseWindow :=
    unary_cont_closed metricDenseUnary wUnary denseWindowRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denseWindowUnary tUnary toleranceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceReadUnary rUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary kUnary sealRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary eUnary boundaryRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryReadUnary hUnary replayRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed replayReadUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
              hsame row K ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨publicRead, hsame_refl publicRead, publicReadUnary⟩
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
                  (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact
    ⟨cert, metricDenseUnary, denseWindowUnary, toleranceReadUnary, regularReadUnary,
      sealReadUnary, boundaryReadUnary, replayReadUnary, publicReadUnary⟩

end BEDC.Derived.CompleteSeparableMetricUp
