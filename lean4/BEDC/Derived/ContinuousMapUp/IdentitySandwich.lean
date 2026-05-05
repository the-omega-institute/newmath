import BEDC.Derived.ContinuousMapUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousUp

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
                                  hsame mapL map ∧ hsame mapR map ∧ hsame modL modulus ∧
                                    hsame modR modulus ∧ hsame certL cert ∧
                                      hsame certR cert ∧ hsame certL certR := by
  intro carrier mapLFRel modLFRel certLFRel mapLRel modLRel certLRel mapRTRel modRTRel
    certRTRel mapRRel modRRel certRRel
  have sameMapLF : hsame mapLF map := cont_left_unit_result mapLFRel
  have sameMapL : hsame mapL map := hsame_trans (cont_right_unit_result mapLRel) sameMapLF
  have sameModLF : hsame modLF modulus := cont_left_unit_result modLFRel
  have sameModL : hsame modL modulus := hsame_trans (cont_right_unit_result modLRel) sameModLF
  have sameCertLF : hsame certLF cert :=
    cont_respects_hsame (hsame_refl target) sameModLF certLFRel carrier.left.right.right.right.right.right
  have sameCertL : hsame certL cert :=
    hsame_trans
      (cont_respects_hsame (hsame_refl target) (cont_right_unit_result modLRel) certLRel
        certLFRel)
      sameCertLF
  have sameMapRT : hsame mapRT map := cont_right_unit_result mapRTRel
  have sameMapR : hsame mapR map := hsame_trans (cont_left_unit_result mapRRel) sameMapRT
  have sameModRT : hsame modRT modulus := cont_right_unit_result modRTRel
  have sameModR : hsame modR modulus := hsame_trans (cont_left_unit_result modRRel) sameModRT
  have sameCertRT : hsame certRT cert :=
    cont_respects_hsame (hsame_refl target) sameModRT certRTRel carrier.left.right.right.right.right.right
  have sameCertR : hsame certR cert :=
    hsame_trans
      (cont_respects_hsame (hsame_refl target) (cont_left_unit_result modRRel) certRRel
        certRTRel)
      sameCertRT
  have leftGraph : Cont source mapL target := by
    cases sameMapL
    exact carrier.left.right.right.right.right.left
  have rightGraph : Cont source mapR target := by
    cases sameMapR
    exact carrier.left.right.right.right.right.left
  have leftFunction :
      ContinuousFunctionCarrier source mapL target modL certL :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.left
        (And.intro (unary_transport carrier.left.right.right.left (hsame_symm sameMapL))
          (And.intro (unary_transport carrier.left.right.right.right.left (hsame_symm sameModL))
            (And.intro leftGraph certLRel))))
  have rightFunction :
      ContinuousFunctionCarrier source mapR target modR certR :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.left
        (And.intro (unary_transport carrier.left.right.right.left (hsame_symm sameMapR))
          (And.intro (unary_transport carrier.left.right.right.right.left (hsame_symm sameModR))
            (And.intro rightGraph certRRel))))
  have leftCarrier :
      ContinuousMapCarrier source mapL target modL certL (append source target) :=
    ContinuousMapCarrier_canonical_distance_iff.mpr leftFunction
  have rightCarrier :
      ContinuousMapCarrier source mapR target modR certR (append source target) :=
    ContinuousMapCarrier_canonical_distance_iff.mpr rightFunction
  exact And.intro leftCarrier
    (And.intro rightCarrier
      (And.intro sameMapL
        (And.intro sameMapR
          (And.intro sameModL
            (And.intro sameModR
              (And.intro sameCertL
                (And.intro sameCertR (hsame_trans sameCertL (hsame_symm sameCertR)))))))))

end BEDC.Derived.ContinuousMapUp
