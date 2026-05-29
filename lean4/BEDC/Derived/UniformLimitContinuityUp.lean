import BEDC.Derived.UniformLimitUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive UniformLimitContinuityUp : Type where
  | mk
      (family sharedModulus tailLedger regularHandoff realSeal continuousGraph
        uniformConsumer transport replay provenance localName : BHist) :
      UniformLimitContinuityUp
  deriving DecidableEq

theorem UniformLimitContinuityUp_seal_factorization_consumer_handoff [AskSetup]
    [PackageSetup]
    {family sharedModulus tailLedger regularHandoff sealRow endpoint continuousGraph
      consumer transport replay provenance localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformLimitUp.UniformLimitCarrier family sharedModulus tailLedger regularHandoff sealRow
        endpoint transport replay provenance localName bundle pkg ->
      Cont regularHandoff sealRow endpoint ->
        Cont endpoint localName publicRead ->
          Cont endpoint continuousGraph consumer ->
            exists packet : UniformLimitContinuityUp,
              packet = UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff
                endpoint continuousGraph consumer transport replay provenance localName ∧
                UnaryHistory family ∧ UnaryHistory sharedModulus ∧ UnaryHistory tailLedger ∧
                  UnaryHistory regularHandoff ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                    UnaryHistory publicRead ∧ Cont family sharedModulus tailLedger ∧
                      Cont tailLedger regularHandoff sealRow ∧
                        Cont regularHandoff sealRow endpoint ∧ PkgSig bundle endpoint pkg ∧
                          Cont endpoint continuousGraph consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory UniformLimitContinuityUp
  intro carrier regularSealEndpoint endpointNamePublicRead endpointContinuousConsumer
  have factorized :=
    UniformLimitUp.UniformLimitCarrier_seal_factorization carrier regularSealEndpoint
      endpointNamePublicRead
  exact
    Exists.intro
      (UniformLimitContinuityUp.mk family sharedModulus tailLedger regularHandoff endpoint
        continuousGraph consumer transport replay provenance localName)
      ⟨rfl,
        factorized.left,
        factorized.right.left,
        factorized.right.right.left,
        factorized.right.right.right.left,
        factorized.right.right.right.right.left,
        factorized.right.right.right.right.right.left,
        factorized.right.right.right.right.right.right.left,
        factorized.right.right.right.right.right.right.right.left,
        factorized.right.right.right.right.right.right.right.right.left,
        factorized.right.right.right.right.right.right.right.right.right.left,
        factorized.right.right.right.right.right.right.right.right.right.right,
        endpointContinuousConsumer⟩

end BEDC.Derived
