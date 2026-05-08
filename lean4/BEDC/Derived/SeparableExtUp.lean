import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SeparableExtSourceSurface
    (fieldExt polynomial generator minimal simpleRoot provenance ledger : BHist) : Prop :=
  UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory generator ∧
    Cont fieldExt polynomial minimal ∧ Cont minimal generator simpleRoot ∧
      Cont simpleRoot provenance ledger

theorem SeparableExtSourceSurface_classifier_stability
    {fieldExt fieldExt' polynomial polynomial' generator generator' minimal minimal'
      simpleRoot simpleRoot' provenance ledger ledger' : BHist} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance ledger ->
      hsame fieldExt fieldExt' ->
        hsame polynomial polynomial' ->
          hsame generator generator' ->
            Cont fieldExt' polynomial' minimal' ->
              Cont minimal' generator' simpleRoot' ->
                Cont simpleRoot' provenance ledger' ->
                  SeparableExtSourceSurface fieldExt' polynomial' generator' minimal' simpleRoot'
                      provenance ledger' ∧
                    hsame minimal minimal' ∧ hsame simpleRoot simpleRoot' ∧
                      hsame ledger ledger' := by
  intro surface sameField samePolynomial sameGenerator minimalRow simpleRootRow ledgerRow
  have fieldUnary : UnaryHistory fieldExt' :=
    unary_transport surface.left sameField
  have polynomialUnary : UnaryHistory polynomial' :=
    unary_transport surface.right.left samePolynomial
  have generatorUnary : UnaryHistory generator' :=
    unary_transport surface.right.right.left sameGenerator
  have sameMinimal : hsame minimal minimal' :=
    cont_respects_hsame sameField samePolynomial surface.right.right.right.left minimalRow
  have sameSimpleRoot : hsame simpleRoot simpleRoot' :=
    cont_respects_hsame sameMinimal sameGenerator surface.right.right.right.right.left
      simpleRootRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSimpleRoot (hsame_refl provenance)
      surface.right.right.right.right.right ledgerRow
  exact And.intro
    (And.intro fieldUnary
      (And.intro polynomialUnary
        (And.intro generatorUnary (And.intro minimalRow (And.intro simpleRootRow ledgerRow)))))
    (And.intro sameMinimal (And.intro sameSimpleRoot sameLedger))

end BEDC.Derived.SeparableExtUp
