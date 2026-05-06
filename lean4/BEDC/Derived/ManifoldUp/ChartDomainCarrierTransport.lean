import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldAtlasPackage_chart_domain_carrier_transport
    {base index domain chart transition base' index' domain' chart' transition' point point' :
      BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      ManifoldAtlasClassifier base index domain chart transition base' index' domain' chart'
        transition' ->
        Cont base point domain -> hsame point point' -> UnaryHistory point' ->
          Cont base' point' domain' ∧ UnaryHistory domain' := by
  intro package classified domainPoint samePoint pointUnary
  have baseSame : hsame base base' := classified.left
  have domainSame : hsame domain domain' := classified.right.right.left
  have transportedDomain : Cont base' point' domain' :=
    cont_hsame_transport baseSame samePoint domainSame domainPoint
  have baseUnary : UnaryHistory base' :=
    unary_transport package.left baseSame
  have domainUnary : UnaryHistory domain' :=
    unary_cont_closed baseUnary pointUnary transportedDomain
  exact And.intro transportedDomain domainUnary

end BEDC.Derived.ManifoldUp
