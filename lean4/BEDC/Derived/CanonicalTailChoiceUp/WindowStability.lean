import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_window_stability
    {M E I T S R H C0 P N tail tail' : BHist}
    (mUnary : UnaryHistory M)
    (eUnary : UnaryHistory E)
    (tUnary : UnaryHistory T)
    (indexRoute : Cont M E I)
    (tailRoute : Cont I T tail)
    (sameTail : hsame tail' tail) :
    UnaryHistory I ∧ UnaryHistory tail ∧ UnaryHistory tail' ∧
      Cont M E I ∧ Cont I T tail := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  have indexUnary : UnaryHistory I :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed indexUnary tUnary tailRoute
  have tailPrimeUnary : UnaryHistory tail' :=
    unary_transport tailUnary (hsame_symm sameTail)
  have _sealRow : hsame S S := hsame_refl S
  have _refusalRow : hsame R R := hsame_refl R
  have _transportRow : hsame H H := hsame_refl H
  have _replayRow : hsame C0 C0 := hsame_refl C0
  have _provenanceRow : hsame P P := hsame_refl P
  have _nameRow : hsame N N := hsame_refl N
  exact ⟨indexUnary, tailUnary, tailPrimeUnary, indexRoute, tailRoute⟩

end BEDC.Derived.CanonicalTailChoiceUp
