import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceMetricCompactnessUnblock [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead finiteNetRead compactRead
      metricCompactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 K1 subsetRead ->
        Cont N0 N1 netRead ->
          Cont subsetRead netRead finiteNetRead ->
            Cont finiteNetRead D0 compactRead ->
              Cont compactRead C metricCompactRead ->
                PkgSig bundle metricCompactRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row metricCompactRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                          hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                            hsame row Hs ∨ hsame row C ∨ hsame row P ∨
                              hsame row M ∨ hsame row finiteNetRead ∨
                                hsame row compactRead ∨ hsame row metricCompactRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle metricCompactRead pkg)
                      hsame ∧ UnaryHistory compactRead ∧
                    UnaryHistory metricCompactRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier subsetRoute netRoute finiteNetRoute compactRoute metricRoute metricPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, _d1Unary,
    _rUnary, _hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed subsetUnary netUnary finiteNetRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed finiteNetUnary d0Unary compactRoute
  have metricUnary : UnaryHistory metricCompactRead :=
    unary_cont_closed compactUnary cUnary metricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricCompactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
                  hsame row finiteNetRead ∨ hsame row compactRead ∨
                    hsame row metricCompactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle metricCompactRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro metricCompactRead ⟨hsame_refl metricCompactRead, metricUnary⟩
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
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, metricPkg⟩
  }
  exact ⟨cert, compactUnary, metricUnary⟩

end BEDC.Derived.HyperspaceUp
