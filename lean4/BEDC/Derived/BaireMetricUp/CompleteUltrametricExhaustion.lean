import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCompleteUltrametricExhaustion [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead ultrametricRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead R metricRead →
            Cont metricRead U ultrametricRead →
              Cont ultrametricRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                          hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S B prefixRead ∧
                          Cont prefixRead W radiusRead ∧ Cont radiusRead R metricRead ∧
                            Cont metricRead U ultrametricRead ∧
                              Cont ultrametricRead N namedRead ∧
                                PkgSig bundle namedRead pkg)
                      hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory ultrametricRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixCont radiusCont metricCont ultrametricCont nameCont namePkg
  obtain ⟨bUnary, wUnary, _dUnary, rUnary, uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    _provenancePkg, _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusCont
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary rUnary metricCont
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed metricUnary uUnary ultrametricCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ultrametricUnary nUnary nameCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              Cont radiusRead R metricRead ∧ Cont metricRead U ultrametricRead ∧
                Cont ultrametricRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, prefixCont, radiusCont, metricCont, ultrametricCont, nameCont,
          namePkg⟩
  }
  exact
    ⟨cert, prefixUnary, radiusUnary, metricUnary, ultrametricUnary, namedUnary⟩

end BEDC.Derived.BaireMetricUp
