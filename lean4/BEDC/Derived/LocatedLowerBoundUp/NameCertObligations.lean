import BEDC.Derived.LocatedLowerBoundUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedLowerBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LocatedLowerBoundCarrier_namecert_obligations
    (x : BEDC.Derived.LocatedLowerBoundUp) :
    (∃ F L W R E H C P N : BHist,
        x = BEDC.Derived.LocatedLowerBoundUp.mk F L W R E H C P N ∧
          hsame F F ∧ hsame L L ∧ hsame E E ∧ hsame N N) ∧
      NameCert
        (fun row : BHist =>
          ∃ F L W R E H C P N : BHist,
            x = BEDC.Derived.LocatedLowerBoundUp.mk F L W R E H C P N ∧
              hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist NameCert hsame
  cases x with
  | mk F L W R E H C P N =>
      constructor
      · exact
          ⟨F, L, W, R, E, H, C, P, N, rfl, hsame_refl F, hsame_refl L,
            hsame_refl E, hsame_refl N⟩
      · exact {
          carrier_inhabited :=
            Exists.intro N
              ⟨F, L, W, R, E, H, C, P, N, rfl, hsame_refl N⟩
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
            cases source with
            | intro F source =>
                cases source with
                | intro L source =>
                    cases source with
                    | intro W source =>
                        cases source with
                        | intro R source =>
                            cases source with
                            | intro E source =>
                                cases source with
                                | intro H source =>
                                    cases source with
                                    | intro C source =>
                                        cases source with
                                        | intro P source =>
                                            cases source with
                                            | intro N source =>
                                                exact
                                                  ⟨F, L, W, R, E, H, C, P, N, source.left,
                                                    hsame_trans (hsame_symm sameRows)
                                                      source.right⟩
        }

end BEDC.Derived.LocatedLowerBoundUp
