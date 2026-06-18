import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def BishopCompletionComparisonCarrier (R B L E T H K P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  UnaryHistory R ∧ UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory E ∧
    UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont R B L ∧ Cont L E T

theorem BishopCompletionComparisonCarrier_namecert_obligations {R B L E T H K P N : BHist} :
    BishopCompletionComparisonCarrier R B L E T H K P N →
      SemanticNameCert
          (fun row : BHist => hsame row T ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row B ∨ hsame row L ∨ hsame row E ∨
              hsame row T ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row T ∧ Cont R B L ∧ Cont L E T)
          hsame ∧
        UnaryHistory R ∧ UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory E ∧
          UnaryHistory T ∧ Cont R B L ∧ Cont L E T := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier
  obtain ⟨rUnary, bUnary, lUnary, eUnary, tUnary, _hUnary, _kUnary, _pUnary, _nUnary,
    routeRB, routeLE⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row T ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row B ∨ hsame row L ∨ hsame row E ∨
              hsame row T ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row T ∧ Cont R B L ∧ Cont L E T)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro T ⟨hsame_refl T, tUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, routeRB, routeLE⟩
    }
  exact ⟨cert, rUnary, bUnary, lUnary, eUnary, tUnary, routeRB, routeLE⟩

end BEDC.Derived.BishopCompletionComparisonUp
