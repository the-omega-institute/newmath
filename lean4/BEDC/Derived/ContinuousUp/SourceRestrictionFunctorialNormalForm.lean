import BEDC.Derived.ContinuousUp.SourceRestriction

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_functorial_normal_form
    {p q sourceT sourceU sourceV sourceW map target targetD targetS oldMod oldCert delta1
      delta2 delta cert certD certS : BHist} :
    Cont sourceU BHist.Empty sourceT ->
      Cont sourceV BHist.Empty sourceU ->
        Cont sourceW BHist.Empty sourceV ->
          ContinuousFunctionCarrier (append p sourceT) map (append p target) (append oldMod q)
              (append (append p oldCert) q) ->
            ContinuousModulusChain target delta1 delta2 cert ->
              Cont delta1 delta2 delta ->
                ContinuousFunctionCarrier (append p sourceW) map (append p targetD)
                    (append delta q) (append (append p certD) q) ->
                  ContinuousFunctionCarrier (append p sourceW) map (append p targetS)
                      (append delta q) (append (append p certS) q) ->
                    ContinuousFunctionCarrier (append p sourceW) map (append p target)
                        (append delta q) (append (append p cert) q) ∧
                      hsame target targetD ∧ hsame cert certD ∧ hsame target targetS ∧
                        hsame cert certS := by
  intro restrictU restrictV restrictW carrier chain compositeRel displayedDirect
    displayedSuccessive
  have restrictWToT : Cont sourceW BHist.Empty sourceT :=
    restrictU.trans (restrictV.trans restrictW)
  have directPackage :=
    ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_commutes restrictWToT
      carrier chain compositeRel displayedDirect
  have successiveReadback :
      hsame target targetS ∧ hsame cert certS :=
    ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic
      directPackage.left displayedSuccessive
  exact And.intro directPackage.left
    (And.intro directPackage.right.right.left
      (And.intro directPackage.right.right.right
        (And.intro successiveReadback.left successiveReadback.right)))

end BEDC.Derived.ContinuousUp
