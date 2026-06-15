import BEDC.Derived.FanBarRouteUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FanBarRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FanBarRouteNameCertObligations (x : FanBarRouteUp) :
    SemanticNameCert
      (fun row : BHist =>
        exists T B I W Q D E H C P N : BHist,
          x = FanBarRouteUp.mk T B I W Q D E H C P N ∧ hsame row N)
      (fun row : BHist =>
        exists T B I W Q D E H C P N : BHist,
          x = FanBarRouteUp.mk T B I W Q D E H C P N ∧ hsame row N)
      (fun row : BHist =>
        exists T B I W Q D E H C P N : BHist,
          x = FanBarRouteUp.mk T B I W Q D E H C P N ∧ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk T B I W Q D E H C P N =>
      exact {
        core := {
          carrier_inhabited := by
            exact
              Exists.intro N
                (Exists.intro T
                  (Exists.intro B
                    (Exists.intro I
                      (Exists.intro W
                        (Exists.intro Q
                          (Exists.intro D
                            (Exists.intro E
                              (Exists.intro H
                                (Exists.intro C
                                  (Exists.intro P
                                    (Exists.intro N
                                      ⟨rfl, hsame_refl N⟩)))))))))))
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
            intro row other sameRows source
            obtain
              ⟨T', B', I', W', Q', D', E', H', C', P', N', carrierEq, sameRow⟩ :=
                source
            exact
              Exists.intro T'
                (Exists.intro B'
                  (Exists.intro I'
                    (Exists.intro W'
                      (Exists.intro Q'
                        (Exists.intro D'
                          (Exists.intro E'
                            (Exists.intro H'
                              (Exists.intro C'
                                (Exists.intro P'
                                  (Exists.intro N'
                                    ⟨carrierEq,
                                      hsame_trans (hsame_symm sameRows) sameRow⟩))))))))))
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.FanBarRouteUp
