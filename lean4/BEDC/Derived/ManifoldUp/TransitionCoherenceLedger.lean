import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive ManifoldTransitionCoherenceLedger
    (i j k self pair triple inverse cocycle : BHist) : BHist -> Prop where
  | identity :
      Cont i i self ->
        ManifoldTransitionCoherenceLedger i j k self pair triple inverse cocycle self
  | inverse :
      Cont self pair inverse ->
        ManifoldTransitionCoherenceLedger i j k self pair triple inverse cocycle inverse
  | cocycle :
      Cont triple self cocycle ->
        ManifoldTransitionCoherenceLedger i j k self pair triple inverse cocycle cocycle

theorem ManifoldTransitionCoherenceLedger_exhaustion
    {i j k self pair triple inverse cocycle ledger : BHist} :
    ManifoldTransitionCoherenceLedger i j k self pair triple inverse cocycle ledger ->
      (hsame ledger self ∧ Cont i i ledger) ∨
        (hsame ledger inverse ∧ Cont self pair ledger) ∨
          (hsame ledger cocycle ∧ Cont triple self ledger) := by
  intro ledgerRow
  cases ledgerRow with
  | identity selfRow =>
      exact Or.inl (And.intro (hsame_refl self) selfRow)
  | inverse inverseRow =>
      exact Or.inr (Or.inl (And.intro (hsame_refl inverse) inverseRow))
  | cocycle cocycleRow =>
      exact Or.inr (Or.inr (And.intro (hsame_refl cocycle) cocycleRow))

end BEDC.Derived.ManifoldUp
