import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_append_multiplier_split_exists {d w q r : BHist} :
    UnaryHistory d -> UnaryHistory w -> UnaryHistory q -> NatMul d (append w q) r ->
      ∃ n : BHist, ∃ e : BHist, UnaryHistory n ∧ UnaryHistory e ∧
        NatMul d w n ∧ NatMul d q e ∧ Cont n e r := by
  intro dUnary wUnary qUnary combined
  have leftTotal := NatMul_total dUnary wUnary
  cases leftTotal with
  | intro n nData =>
      have rightTotal := NatMul_total dUnary qUnary
      cases rightTotal with
      | intro e eData =>
          have displayedProduct : NatMul d (append w q) (append n e) :=
            NatMul_append_cont nData.right eData.right (cont_intro rfl)
          have sameResult : hsame r (append n e) :=
            NatMul_functional dUnary combined displayedProduct
          have displayed : Cont n e r :=
            cont_result_hsame_transport (cont_intro rfl) (hsame_symm sameResult)
          exact ⟨n, e, nData.left, eData.left, nData.right, eData.right, displayed⟩

end BEDC.Derived.PrimeUp
