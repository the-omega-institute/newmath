import BEDC.Derived.RegularCauchyMinUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RegularCauchyMinIdempotentSelectorSurface
    (A W DA J S R E : BHist) (h : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame NameCert
  hsame h A \/ hsame h W \/ hsame h DA \/ hsame h J \/ hsame h S \/
    hsame h R \/ hsame h E

theorem RegularCauchyMinSelector_idempotence_certificate
    (A W DA J S R E H C P N : BHist) :
    NameCert
        (RegularCauchyMinIdempotentSelectorSurface A W DA J S R E)
        hsame /\
      regularCauchyMinFields
          (RegularCauchyMinUp.mk A A W DA DA J S R E H C P N) =
        [A, A, W, DA, DA, J, S, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  constructor
  · exact {
      carrier_inhabited :=
        Exists.intro A (Or.inl (hsame_refl A))
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
        | inl sameA =>
            exact Or.inl (hsame_trans (hsame_symm same) sameA)
        | inr rest =>
            cases rest with
            | inl sameW =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameW))
            | inr rest =>
                cases rest with
                | inl sameDA =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameDA)))
                | inr rest =>
                    cases rest with
                    | inl sameJ =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameJ))))
                    | inr rest =>
                        cases rest with
                        | inl sameS =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl (hsame_trans (hsame_symm same) sameS)))))
                        | inr rest =>
                            cases rest with
                            | inl sameR =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm same) sameR))))))
                            | inr sameE =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (hsame_trans (hsame_symm same) sameE))))))
    }
  · rfl

end BEDC.Derived.RegularCauchyMinUp
