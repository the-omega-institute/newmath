import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RingOfIntegersUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RingOfIntegersDedekindSourceCarrier [AskSetup] [PackageSetup]
    (numField int embedding equation classifier cont provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory numField ∧ UnaryHistory int ∧ UnaryHistory equation ∧ UnaryHistory cont ∧
    Cont numField int embedding ∧ Cont embedding equation classifier ∧
      Cont classifier cont endpoint ∧ PkgSig bundle endpoint pkg ∧
        hsame provenance BHist.Empty

theorem RingOfIntegersDedekindSourceCarrier_integral_equation_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {numField int embedding equation classifier cont provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RingOfIntegersDedekindSourceCarrier numField int embedding equation classifier cont
      provenance endpoint bundle pkg ->
      UnaryHistory embedding ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
        hsame embedding (append numField int) ∧
          hsame classifier (append embedding equation) ∧
            hsame endpoint (append classifier cont) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have contEmbedding : Cont numField int embedding := carrier.right.right.right.right.left
  have contClassifier : Cont embedding equation classifier :=
    carrier.right.right.right.right.right.left
  have contEndpoint : Cont classifier cont endpoint :=
    carrier.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.left
  have sameEmbedding : hsame embedding (append numField int) := contEmbedding
  have sameClassifier : hsame classifier (append embedding equation) := contClassifier
  have sameEndpoint : hsame endpoint (append classifier cont) := contEndpoint
  have unaryEmbedding : UnaryHistory embedding := by
    cases sameEmbedding
    exact unary_append_closed carrier.left carrier.right.left
  have unaryClassifier : UnaryHistory classifier := by
    cases sameClassifier
    exact unary_append_closed unaryEmbedding carrier.right.right.left
  have unaryEndpoint : UnaryHistory endpoint := by
    cases sameEndpoint
    exact unary_append_closed unaryClassifier carrier.right.right.right.left
  exact And.intro unaryEmbedding
    (And.intro unaryClassifier
      (And.intro unaryEndpoint
        (And.intro sameEmbedding
          (And.intro sameClassifier
            (And.intro sameEndpoint pkgSig)))))

end BEDC.Derived.RingOfIntegersUp
