import BEDC.Derived.PrimeUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MulupSemanticExitAndDivisibilityOrderPhasePackage {d q n : BHist} :
    NatMul d q n ->
      UnaryHistory d ∧ UnaryHistory q ∧ UnaryHistory n ∧ NatDivides d n ∧
        SemanticNameCert
          (fun row : BHist => hsame row n ∧ UnaryHistory row)
          (fun row : BHist => hsame row n ∧ NatDivides d n ∧ NatMul d q n)
          (fun row : BHist => hsame row n ∧ UnaryHistory row ∧ NatDivides d n)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame NatMul NatDivides SemanticNameCert UnaryHistory
  intro mul
  have dUnary : UnaryHistory d := NatMul_left_unary mul
  have qUnary : UnaryHistory q := NatMul_right_unary mul
  have nUnary : UnaryHistory n := NatMul_result_unary dUnary mul
  have divides : NatDivides d n := Exists.intro q ⟨qUnary, mul⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row n ∧ UnaryHistory row)
        (fun row : BHist => hsame row n ∧ NatDivides d n ∧ NatMul d q n)
        (fun row : BHist => hsame row n ∧ UnaryHistory row ∧ NatDivides d n)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro n ⟨hsame_refl n, nUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, divides, mul⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, source.right, divides⟩
  }
  exact ⟨dUnary, qUnary, nUnary, divides, cert⟩

theorem MulupFullNatArithmeticPhaseExitBoundary {d q n : BHist} :
    NatMul d q n ->
      UnaryHistory d ∧ UnaryHistory q ∧ UnaryHistory n ∧ NatDivides d n ∧
        NatDivides (BHist.e1 BHist.Empty) n ∧
          SemanticNameCert
            (fun row : BHist => hsame row n ∧ UnaryHistory row)
            (fun row : BHist => hsame row n ∧ (NatMul d q n ∨ NatDivides d row))
            (fun row : BHist =>
              hsame row n ∧ UnaryHistory row ∧ NatDivides (BHist.e1 BHist.Empty) n)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame NatMul NatDivides SemanticNameCert UnaryHistory
  intro mul
  have dUnary : UnaryHistory d := NatMul_left_unary mul
  have qUnary : UnaryHistory q := NatMul_right_unary mul
  have nUnary : UnaryHistory n := NatMul_result_unary dUnary mul
  have divides : NatDivides d n := Exists.intro q ⟨qUnary, mul⟩
  have unitDivides : NatDivides (BHist.e1 BHist.Empty) n :=
    (NatDivides_unit_self_reflexive nUnary).left
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row n ∧ UnaryHistory row)
        (fun row : BHist => hsame row n ∧ (NatMul d q n ∨ NatDivides d row))
        (fun row : BHist =>
          hsame row n ∧ UnaryHistory row ∧ NatDivides (BHist.e1 BHist.Empty) n)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro n ⟨hsame_refl n, nUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, Or.inl mul⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, source.right, unitDivides⟩
  }
  exact ⟨dUnary, qUnary, nUnary, divides, unitDivides, cert⟩

end BEDC.Derived.PrimeUp
