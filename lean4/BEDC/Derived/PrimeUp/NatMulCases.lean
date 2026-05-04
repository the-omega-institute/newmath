import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatMul_exponent_result_cases {d q n : BHist} :
    NatMul d q n ->
      (hsame q BHist.Empty ∧ hsame n BHist.Empty) ∨
        ∃ tail pred : BHist, q = BHist.e1 tail ∧ NatMul d tail pred ∧ Cont pred d n := by
  intro mul
  cases mul with
  | zero _hd =>
      exact Or.inl ⟨rfl, rfl⟩
  | succ previous step =>
      exact Or.inr ⟨_, _, rfl, previous, step⟩

theorem NatDivides_result_cases {d n : BHist} :
    NatDivides d n ->
      (hsame n BHist.Empty ∧ UnaryHistory d) ∨
        ∃ pred : BHist, NatDivides d pred ∧ Cont pred d n := by
  intro divides
  cases divides with
  | intro q data =>
      cases data with
      | intro qUnary mul =>
          cases mul with
          | zero dUnary =>
              exact Or.inl ⟨rfl, dUnary⟩
          | succ previous step =>
              exact Or.inr ⟨_, ⟨_, unary_e1_inversion qUnary, previous⟩, step⟩

end BEDC.Derived.PrimeUp
