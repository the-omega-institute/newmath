import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.Dyadic_interval_netUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DyadicIntervalNetCarrier (D J E S R Q H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory D ∧ UnaryHistory J ∧ UnaryHistory E ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont D J E ∧ Cont E S R ∧
        Cont R Q C ∧ hsame H (append D J)

theorem DyadicIntervalNetCoverRefinement
    {D J E S R Q H C P N refinedRead witnessRead : BHist} :
    DyadicIntervalNetCarrier D J E S R Q H C P N → Cont J E refinedRead →
      Cont S R witnessRead →
        SemanticNameCert
            (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row D ∨ hsame row J ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨
                hsame row Q ∨ hsame row refinedRead ∨ hsame row witnessRead)
            (fun row : BHist => UnaryHistory row ∧ Cont J E refinedRead ∧
              Cont S R witnessRead)
            hsame ∧
          UnaryHistory refinedRead ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier refinedRoute witnessRoute
  rcases carrier with
    ⟨_dUnary, jUnary, eUnary, sUnary, rUnary, _qUnary, _hUnary, _cUnary, _pUnary,
      _nUnary, _sourceRoute, _windowRoute, _consumerRoute, _transportRoute⟩
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed jUnary eUnary refinedRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed sUnary rUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row J ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨
              hsame row Q ∨ hsame row refinedRead ∨ hsame row witnessRead)
          (fun row : BHist => UnaryHistory row ∧ Cont J E refinedRead ∧
            Cont S R witnessRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refinedRoute, witnessRoute⟩
  }
  exact ⟨cert, refinedUnary, witnessUnary⟩

end BEDC.Derived.Dyadic_interval_netUp
