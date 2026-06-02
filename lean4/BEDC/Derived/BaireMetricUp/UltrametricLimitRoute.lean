import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_obligation_ultrametric_limit_route [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead ultrametricRead limitRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead U ultrametricRead →
              Cont ultrametricRead R limitRead →
                PkgSig bundle limitRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                          hsame row R ∨ hsame row U ∨ hsame row prefixRead ∨
                            hsame row radiusRead ∨ hsame row metricRead ∨
                              hsame row ultrametricRead ∨ hsame row limitRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S B prefixRead ∧
                          Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                            Cont metricRead U ultrametricRead ∧
                              Cont ultrametricRead R limitRead ∧
                                PkgSig bundle limitRead pkg)
                      hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory ultrametricRead ∧
                  UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute ultrametricRoute limitRoute limitPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    _carrierPkg, _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed metricUnary uUnary ultrametricRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed ultrametricUnary rUnary limitRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row prefixRead ∨ hsame row radiusRead ∨
                hsame row metricRead ∨ hsame row ultrametricRead ∨ hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead U ultrametricRead ∧
                Cont ultrametricRead R limitRead ∧ PkgSig bundle limitRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRead ⟨hsame_refl limitRead, limitUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, ultrametricRoute, limitRoute,
          limitPkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary, metricUnary, ultrametricUnary, limitUnary⟩

end BEDC.Derived.BaireMetricUp
