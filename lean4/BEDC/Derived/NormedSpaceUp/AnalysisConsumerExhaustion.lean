import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_consumer_exhaustion [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead completionRead structuralRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      Cont V R normRead →
        Cont normRead M metricRead →
          Cont metricRead Q completionRead →
            Cont completionRead H structuralRead →
              Cont structuralRead C consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                          hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                            hsame row C ∨ hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle consumerRead pkg)
                      hsame ∧
                    UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory structuralRead ∧
                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier normRoute metricRoute completionRoute structuralRoute consumerRoute consumerPkg
  obtain ⟨vUnary, rUnary, _nUnary, mUnary, qUnary, hUnary, _tUnary, _pUnary,
    cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vUnary rUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normReadUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed completionReadUnary hUnary structuralRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed structuralReadUnary cUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, consumerPkg⟩
  }
  exact
    ⟨cert, normReadUnary, metricReadUnary, completionReadUnary, structuralReadUnary,
      consumerReadUnary⟩

end BEDC.Derived.NormedSpaceUp
