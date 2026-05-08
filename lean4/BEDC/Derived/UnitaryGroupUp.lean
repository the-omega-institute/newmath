import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitaryGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem UnitaryGroupCarrier_classifier_obligation
    {hilbert hilbert' automorphism automorphism' source source' target target' : BHist} :
    UnaryHistory hilbert -> UnaryHistory automorphism -> hsame hilbert hilbert' ->
      hsame automorphism automorphism' -> Cont hilbert automorphism source ->
        Cont hilbert' automorphism' source' -> Cont automorphism hilbert target ->
          Cont automorphism' hilbert' target' ->
            UnaryHistory hilbert' ∧ UnaryHistory automorphism' ∧
              hsame source source' ∧ hsame target target' := by
  intro unaryHilbert unaryAutomorphism sameHilbert sameAutomorphism sourceRow sourceRow'
    targetRow targetRow'
  have unaryHilbert' : UnaryHistory hilbert' :=
    unary_transport unaryHilbert sameHilbert
  have unaryAutomorphism' : UnaryHistory automorphism' :=
    unary_transport unaryAutomorphism sameAutomorphism
  have sameSource : hsame source source' :=
    cont_respects_hsame sameHilbert sameAutomorphism sourceRow sourceRow'
  have sameTarget : hsame target target' :=
    cont_respects_hsame sameAutomorphism sameHilbert targetRow targetRow'
  exact And.intro unaryHilbert'
    (And.intro unaryAutomorphism' (And.intro sameSource sameTarget))

theorem UnitaryGroupOperation_stability_obligation
    {left left' right right' product product' inverse inverse' identity identity' : BHist} :
    hsame inverse inverse' -> hsame identity identity' -> hsame right right' ->
      Cont inverse identity left -> Cont inverse' identity' left' ->
        Cont left right product -> Cont left' right' product' ->
          hsame left left' ∧ hsame product product' := by
  intro sameInverse sameIdentity sameRight inverseIdentityRow inverseIdentityRow'
    productRow productRow'
  have sameLeft : hsame left left' :=
    cont_respects_hsame sameInverse sameIdentity inverseIdentityRow inverseIdentityRow'
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameLeft sameRight productRow productRow'
  exact And.intro sameLeft sameProduct

end BEDC.Derived.UnitaryGroupUp
