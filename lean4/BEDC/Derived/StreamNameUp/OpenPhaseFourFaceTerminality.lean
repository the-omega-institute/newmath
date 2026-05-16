import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameFiniteWindowClassifier_open_phase_four_face_terminality
    {s t : BHist -> BHist} {window dyadic regseq real : BHist} :
    RatStreamNameFiniteWindowClassifier s t
        (ProbeBundle.Bcons window
          (ProbeBundle.Bcons dyadic
            (ProbeBundle.Bcons regseq (ProbeBundle.Bcons real ProbeBundle.Bnil)))) ->
      UnaryHistory window ->
        UnaryHistory dyadic ->
          UnaryHistory regseq ->
            UnaryHistory real ->
              RatHistoryClassifier (s window) (t window) ∧
                RatHistoryClassifier (s dyadic) (t dyadic) ∧
                  RatHistoryClassifier (s regseq) (t regseq) ∧
                    RatHistoryClassifier (s real) (t real) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle UnaryHistory RatHistoryClassifier
  intro classified windowUnary dyadicUnary regseqUnary realUnary
  have windowIn :
      InBundle window
        (ProbeBundle.Bcons window
          (ProbeBundle.Bcons dyadic
            (ProbeBundle.Bcons regseq (ProbeBundle.Bcons real ProbeBundle.Bnil)))) :=
    Or.inl rfl
  have dyadicIn :
      InBundle dyadic
        (ProbeBundle.Bcons window
          (ProbeBundle.Bcons dyadic
            (ProbeBundle.Bcons regseq (ProbeBundle.Bcons real ProbeBundle.Bnil)))) :=
    Or.inr (Or.inl rfl)
  have regseqIn :
      InBundle regseq
        (ProbeBundle.Bcons window
          (ProbeBundle.Bcons dyadic
            (ProbeBundle.Bcons regseq (ProbeBundle.Bcons real ProbeBundle.Bnil)))) :=
    Or.inr (Or.inr (Or.inl rfl))
  have realIn :
      InBundle real
        (ProbeBundle.Bcons window
          (ProbeBundle.Bcons dyadic
            (ProbeBundle.Bcons regseq (ProbeBundle.Bcons real ProbeBundle.Bnil)))) :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  exact
    ⟨classified window windowIn windowUnary, classified dyadic dyadicIn dyadicUnary,
      classified regseq regseqIn regseqUnary, classified real realIn realUnary⟩

end BEDC.Derived.StreamNameUp
