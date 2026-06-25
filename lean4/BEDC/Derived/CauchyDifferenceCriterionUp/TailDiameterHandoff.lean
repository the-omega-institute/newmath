import BEDC.Derived.CauchyDifferenceCriterionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def CauchyDifferenceCriterionTailHandoffSurface
    (X Y D Z Q W T E : BHist) (h : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame NameCert
  hsame h X \/ hsame h Y \/ hsame h D \/ hsame h Z \/ hsame h Q \/
    hsame h W \/ hsame h T \/ hsame h E

theorem CauchyDifferenceCriterionTailDiameter_handoff_certificate
    (X Y D Z Q W T E H C P N : BHist) :
    NameCert
        (CauchyDifferenceCriterionTailHandoffSurface X Y D Z Q W T E)
        hsame /\
      cauchyDifferenceCriterionFields
          (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  constructor
  · exact {
      carrier_inhabited :=
        Exists.intro X (Or.inl (hsame_refl X))
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro h k same source
        cases source with
        | inl sameX =>
            exact Or.inl (hsame_trans (hsame_symm same) sameX)
        | inr rest =>
            cases rest with
            | inl sameY =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameY))
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameD)))
                | inr rest =>
                    cases rest with
                    | inl sameZ =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameZ))))
                    | inr rest =>
                        cases rest with
                        | inl sameQ =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl (hsame_trans (hsame_symm same) sameQ)))))
                        | inr rest =>
                            cases rest with
                            | inl sameW =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm same) sameW))))))
                            | inr rest =>
                                cases rest with
                                | inl sameT =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inl
                                                  (hsame_trans
                                                    (hsame_symm same) sameT)))))))
                                | inr sameE =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (hsame_trans
                                                    (hsame_symm same) sameE)))))))
    }
  · rfl

end BEDC.Derived.CauchyDifferenceCriterionUp
