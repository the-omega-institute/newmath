import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedspaceMetricCompletionSource [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V R normRead ->
        Cont normRead M metricRead ->
          Cont metricRead Q completionRead ->
            Cont metricRead completionRead sourceRead ->
              PkgSig bundle sourceRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                        hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                          hsame row C ∨ hsame row normRead ∨ hsame row metricRead ∨
                            hsame row completionRead ∨ hsame row sourceRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont metricRead Q completionRead ∧
                        Cont metricRead completionRead sourceRead ∧
                          PkgSig bundle sourceRead pkg)
                    hsame ∧
                  UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier normRoute metricRoute completionRoute sourceRoute sourcePkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, _hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg,
    _localPkg⟩ := carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed metricReadUnary completionReadUnary sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row normRead ∨ hsame row metricRead ∨
                  hsame row completionRead ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metricRead Q completionRead ∧
              Cont metricRead completionRead sourceRead ∧ PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceReadUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionRoute, sourceRoute, sourcePkg⟩
  }
  exact ⟨cert, normReadUnary, metricReadUnary, completionReadUnary, sourceReadUnary⟩

end BEDC.Derived.NormedSpaceUp
