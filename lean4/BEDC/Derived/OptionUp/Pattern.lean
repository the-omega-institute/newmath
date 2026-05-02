import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

def OptionHistoryPattern (source : BHist -> Prop) (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ ∃ a : BHist, source a ∧ hsame h a

theorem OptionHistoryPattern_carrier_iff {source : BHist -> Prop}
    (source_transport : ∀ {h k : BHist}, hsame h k -> source h -> source k)
    {h : BHist} :
    OptionHistoryPattern source h ↔ OptionHistoryCarrier source h := by
  constructor
  · intro pattern
    cases pattern with
    | inl emptyCase =>
        exact Or.inl emptyCase
    | inr presentCase =>
        cases presentCase with
        | intro a data =>
            cases data with
            | intro sourceA sameHA =>
                exact Or.inr (source_transport (hsame_symm sameHA) sourceA)
  · intro carrier
    cases carrier with
    | inl emptyCase =>
        exact Or.inl emptyCase
    | inr sourceH =>
        exact Or.inr (Exists.intro h (And.intro sourceH (hsame_refl h)))

end BEDC.Derived.OptionUp
