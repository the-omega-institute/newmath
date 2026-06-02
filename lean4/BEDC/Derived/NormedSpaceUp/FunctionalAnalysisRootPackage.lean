import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedspaceFunctionalAnalysisRootPackage [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead analysisRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont completionRead H analysisRead ->
              Cont analysisRead C rootRead ->
                PkgSig bundle rootRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                          hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row rootRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧
                          Cont analysisRead C rootRead)
                      hsame ∧
                    UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory analysisRead ∧
                        UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier normRoute metricRoute completionRoute analysisRoute rootRoute rootPkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, hUnary, _tUnary, _pUnary, cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg,
      _localPkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary mUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary qUnary completionRoute
  have analysisUnary : UnaryHistory analysisRead :=
    unary_cont_closed completionUnary hUnary analysisRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed analysisUnary cUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧
              Cont analysisRead C rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
              (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootPkg, rootRoute⟩
  }
  exact ⟨cert, normUnary, metricUnary, completionUnary, analysisUnary, rootUnary⟩

end BEDC.Derived.NormedSpaceUp
