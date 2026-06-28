import BEDC.Derived.DyadicTotallyBoundedIntervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicTotallyBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DyadicTotallyBoundedIntervalCarrier_namecert_obligations
    (x : BEDC.Derived.DyadicTotallyBoundedIntervalUp) :
    (∃ L U M Z rho F S R E H C P N : BHist,
        x = BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk L U M Z rho F S R E H C P N ∧
          hsame L L ∧ hsame U U ∧ hsame rho rho ∧ hsame N N) ∧
      NameCert
        (fun row : BHist =>
          ∃ L U M Z rho F S R E H C P N : BHist,
            x = BEDC.Derived.DyadicTotallyBoundedIntervalUp.mk L U M Z rho F S R E H C P N ∧
              hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist NameCert hsame
  cases x with
  | mk L U M Z rho F S R E H C P N =>
      constructor
      · exact
          ⟨L, U, M, Z, rho, F, S, R, E, H, C, P, N, rfl, hsame_refl L,
            hsame_refl U, hsame_refl rho, hsame_refl N⟩
      · exact {
          carrier_inhabited :=
            Exists.intro N
              ⟨L, U, M, Z, rho, F, S, R, E, H, C, P, N, rfl, hsame_refl N⟩
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
            | intro L source =>
                cases source with
                | intro U source =>
                    cases source with
                    | intro M source =>
                        cases source with
                        | intro Z source =>
                            cases source with
                            | intro rho source =>
                                cases source with
                                | intro F source =>
                                    cases source with
                                    | intro S source =>
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
                                                                  ⟨L, U, M, Z, rho, F, S,
                                                                    R, E, H, C, P, N,
                                                                    source.left,
                                                                    hsame_trans
                                                                      (hsame_symm sameRows)
                                                                      source.right⟩
        }

end BEDC.Derived.DyadicTotallyBoundedIntervalUp
