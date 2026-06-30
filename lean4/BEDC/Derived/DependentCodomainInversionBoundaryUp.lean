import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DependentCodomainInversionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive DependentCodomainInversionBoundaryUp : Type where
  | mk
      (Pi A a a' C0 C1 S R O H P N : BHist) :
      DependentCodomainInversionBoundaryUp

def dependentCodomainInversionBoundaryFields :
    DependentCodomainInversionBoundaryUp -> List BHist
  | DependentCodomainInversionBoundaryUp.mk Pi A a a' C0 C1 S R O H P N =>
      [Pi, A, a, a', C0, C1, S, R, O, H, append S R, P, N]

theorem DependentCodomainInversionBoundaryCarrier_namecert_obligations
    (x : DependentCodomainInversionBoundaryUp) :
    exists Pi A a a' C0 C1 S R O H K P N : BHist,
      dependentCodomainInversionBoundaryFields x =
          [Pi, A, a, a', C0, C1, S, R, O, H, K, P, N] ∧
        hsame H H ∧ Cont S R K ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk Pi A a a' C0 C1 S R O H P N =>
      refine
        ⟨Pi, A, a, a', C0, C1, S, R, O, H, append S R, P, N, ?_⟩
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
      · rfl
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

end BEDC.Derived.DependentCodomainInversionBoundaryUp
