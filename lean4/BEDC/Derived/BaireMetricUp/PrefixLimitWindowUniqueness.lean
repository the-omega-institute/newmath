import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricPrefixLimitWindowUniqueness [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead metricRead parentRead strongRead limitLeft
      limitRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead R parentRead →
              Cont parentRead U strongRead →
                Cont strongRead C limitLeft →
                  hsame limitLeft limitRight →
                    PkgSig bundle limitRight pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row limitRight ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                              hsame row R ∨ hsame row U ∨ hsame row C ∨
                                hsame row limitLeft ∨ hsame row limitRight)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S B prefixRead ∧
                              Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                                Cont metricRead R parentRead ∧ Cont parentRead U strongRead ∧
                                  Cont strongRead C limitLeft ∧ hsame limitLeft limitRight ∧
                                    PkgSig bundle limitRight pkg)
                          hsame ∧ UnaryHistory limitLeft ∧ UnaryHistory limitRight := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute parentRoute strongRoute limitRoute sameLimits
    limitPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, uUnary, sUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP, _carrierPkg,
    _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed metricUnary rUnary parentRoute
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed parentUnary uUnary strongRoute
  have limitLeftUnary : UnaryHistory limitLeft :=
    unary_cont_closed strongUnary cUnary limitRoute
  have limitRightUnary : UnaryHistory limitRight :=
    unary_transport limitLeftUnary sameLimits
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRight ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ hsame row C ∨ hsame row limitLeft ∨ hsame row limitRight)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead D metricRead ∧ Cont metricRead R parentRead ∧
                Cont parentRead U strongRead ∧ Cont strongRead C limitLeft ∧
                  hsame limitLeft limitRight ∧ PkgSig bundle limitRight pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRight
        ⟨hsame_refl limitRight, limitRightUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, radiusRoute, metricRoute, parentRoute, strongRoute,
          limitRoute, sameLimits, limitPkg⟩
  }
  exact ⟨cert, limitLeftUnary, limitRightUnary⟩

end BEDC.Derived.BaireMetricUp
