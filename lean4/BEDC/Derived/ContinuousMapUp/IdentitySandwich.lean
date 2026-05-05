import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousMapCarrier_identity_sandwich_coherence
    {source target map modulus cert distance mapLF mapL mapRT mapR modLF modL modRT modR
      certLF certL certRT certR : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      Cont BHist.Empty map mapLF ->
        Cont BHist.Empty modulus modLF ->
          Cont target modLF certLF ->
            Cont mapLF BHist.Empty mapL ->
              Cont modLF BHist.Empty modL ->
                Cont target modL certL ->
                  Cont map BHist.Empty mapRT ->
                    Cont modulus BHist.Empty modRT ->
                      Cont target modRT certRT ->
                        Cont BHist.Empty mapRT mapR ->
                          Cont BHist.Empty modRT modR ->
                            Cont target modR certR ->
                              ContinuousMapCarrier source mapL target modL certL
                                  (append source target) ∧
                                ContinuousMapCarrier source mapR target modR certR
                                    (append source target) ∧
                                  hsame mapL map ∧ hsame mapR map ∧
                                    hsame modL modulus ∧ hsame modR modulus ∧
                                      hsame certL cert ∧ hsame certR cert ∧
                                        hsame certL certR := by
  intro carrier graphLF modulusLF certLFRel graphL modulusL certLRel graphRT modulusRT
    certRTRel graphR modulusR certRRel
  have identities := ContinuousMapCarrier_empty_identities_closed carrier
  have leftIntermediate :
      ContinuousMapCarrier source mapLF target modLF certLF (append source target) :=
    ContinuousMapCarrier_comp_closed identities.left carrier graphLF modulusLF certLFRel
  have leftCarrier :
      ContinuousMapCarrier source mapL target modL certL (append source target) :=
    ContinuousMapCarrier_comp_closed leftIntermediate identities.right graphL modulusL certLRel
  have rightIntermediate :
      ContinuousMapCarrier source mapRT target modRT certRT (append source target) :=
    ContinuousMapCarrier_comp_closed carrier identities.right graphRT modulusRT certRTRel
  have rightCarrier :
      ContinuousMapCarrier source mapR target modR certR (append source target) :=
    ContinuousMapCarrier_comp_closed identities.left rightIntermediate graphR modulusR certRRel
  have sameMapL : hsame mapL map :=
    hsame_trans (cont_right_unit_iff.mp graphL) (cont_left_unit_result graphLF)
  have sameMapR : hsame mapR map :=
    hsame_trans (cont_left_unit_result graphR) (cont_right_unit_iff.mp graphRT)
  have sameModL : hsame modL modulus :=
    hsame_trans (cont_right_unit_iff.mp modulusL) (cont_left_unit_result modulusLF)
  have sameModR : hsame modR modulus :=
    hsame_trans (cont_left_unit_result modulusR) (cont_right_unit_iff.mp modulusRT)
  have certRel : Cont target modulus cert := carrier.left.right.right.right.right.right
  have sameCertL : hsame certL cert :=
    cont_respects_hsame (hsame_refl target) sameModL certLRel certRel
  have sameCertR : hsame certR cert :=
    cont_respects_hsame (hsame_refl target) sameModR certRRel certRel
  exact
    And.intro leftCarrier
      (And.intro rightCarrier
        (And.intro sameMapL
          (And.intro sameMapR
            (And.intro sameModL
              (And.intro sameModR
                (And.intro sameCertL
                  (And.intro sameCertR
                    (hsame_trans sameCertL (hsame_symm sameCertR)))))))))

end BEDC.Derived.ContinuousMapUp
