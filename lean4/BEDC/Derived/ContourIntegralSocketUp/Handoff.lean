import BEDC.Derived.ContourIntegralSocketUp

namespace BEDC.Derived.ContourIntegralSocketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ContourIntegralSocketHandoff
    {G F M I L H C P N analyticRead cauchyRead namedRead : BHist} :
    Cont G F analyticRead ->
      Cont analyticRead I namedRead ->
        Cont M L cauchyRead ->
          Cont cauchyRead P namedRead ->
            hsame H C ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row namedRead ∧
                      (hsame row analyticRead ∨ hsame row cauchyRead ∨
                        hsame row namedRead))
                  (fun row : BHist =>
                    hsame row G ∨ hsame row F ∨ hsame row M ∨ hsame row I ∨
                      hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row namedRead)
                  (fun _row : BHist =>
                    Cont G F analyticRead ∧ Cont analyticRead I namedRead ∧
                      Cont M L cauchyRead ∧ Cont cauchyRead P namedRead ∧ hsame H C)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro analyticRoute analyticNamedRoute cauchyRoute cauchyNamedRoute sameTransport
  have sourceNamed :
      (fun row : BHist =>
        hsame row namedRead ∧
          (hsame row analyticRead ∨ hsame row cauchyRead ∨ hsame row namedRead))
        namedRead := by
    exact ⟨hsame_refl namedRead, Or.inr (Or.inr (hsame_refl namedRead))⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
        have sameNamed : hsame _other namedRead :=
          hsame_trans (hsame_symm sameRows) source.left
        exact ⟨sameNamed, Or.inr (Or.inr sameNamed)⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨analyticRoute, analyticNamedRoute, cauchyRoute, cauchyNamedRoute,
          sameTransport⟩
  }

end BEDC.Derived.ContourIntegralSocketUp
