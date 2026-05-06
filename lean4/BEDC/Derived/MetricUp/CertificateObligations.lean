import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricCertificateObligations : Prop :=
  forall {x y : BHist}, UnaryHistory x -> UnaryHistory y ->
    exists d : BHist, UnaryHistory d ∧ Cont x y d

end BEDC.Derived.MetricUp
