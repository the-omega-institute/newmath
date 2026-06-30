import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealCauchyModulusSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive RealCauchyModulusSelectorUp : Type where
  | mk (M S D Q E R H P N : BHist) : RealCauchyModulusSelectorUp

def realCauchyModulusSelectorFields : RealCauchyModulusSelectorUp -> List BHist
  | RealCauchyModulusSelectorUp.mk M S D Q E R H P N =>
      [M, S, D, Q, E, R, H, append R M, P, N]

theorem RealCauchyModulusSelectorCarrier_finite_window_soundness
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro N (hsame_refl N)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row other same
              exact hsame_symm same
            equiv_trans := by
              intro row other third sameRO sameOT
              exact hsame_trans sameRO sameOT
            carrier_respects_equiv := by
              intro row other same source
              exact hsame_trans (hsame_symm same) source
          }

end BEDC.Derived.RealCauchyModulusSelectorUp
