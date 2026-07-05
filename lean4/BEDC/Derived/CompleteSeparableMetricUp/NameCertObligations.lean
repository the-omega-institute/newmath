import BEDC.Derived.CompleteSeparableMetricUp.DensityCompletionHandoff

namespace BEDC.Derived.CompleteSeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompleteSeparableMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M K D W T R E H C P N denseRead toleranceRead regularRead completeRead realRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompleteSeparableMetricCarrier M K D W T R E H C P N bundle pkg ->
      Cont M D denseRead ->
        Cont denseRead W toleranceRead ->
          Cont toleranceRead T regularRead ->
            Cont regularRead R completeRead ->
              Cont completeRead K realRead ->
                Cont realRead P namedRead ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row W ∨
                            hsame row T ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                              hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row denseRead ∨ hsame row toleranceRead ∨
                                  hsame row regularRead ∨ hsame row completeRead ∨
                                    hsame row realRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M D denseRead ∧
                            Cont denseRead W toleranceRead ∧
                              Cont toleranceRead T regularRead ∧
                                Cont regularRead R completeRead ∧
                                  Cont completeRead K realRead ∧
                                    Cont realRead P namedRead ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory denseRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory completeRead ∧
                          UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CompleteSeparableMetricCarrier BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute toleranceRoute regularRoute completeRoute realRoute namedRoute namePkg
  obtain ⟨mUnary, kUnary, dUnary, wUnary, tUnary, rUnary, _eUnary, _hUnary, _cUnary,
    pUnary, _nUnary, _carrierNamePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed mUnary dUnary denseRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denseUnary wUnary toleranceRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed toleranceUnary tUnary regularRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed regularUnary rUnary completeRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed completeUnary kUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary pUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row T ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row denseRead ∨ hsame row toleranceRead ∨
                  hsame row regularRead ∨ hsame row completeRead ∨ hsame row realRead ∨
                    hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead W toleranceRead ∧
              Cont toleranceRead T regularRead ∧ Cont regularRead R completeRead ∧
                Cont completeRead K realRead ∧ Cont realRead P namedRead ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨namedRead, hsame_refl namedRead, namedUnary⟩
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
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr source.left)))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, toleranceRoute, regularRoute, completeRoute, realRoute,
          namedRoute, namePkg⟩
  }
  exact
    ⟨cert, denseUnary, toleranceUnary, regularUnary, completeUnary, realUnary, namedUnary⟩

end BEDC.Derived.CompleteSeparableMetricUp
