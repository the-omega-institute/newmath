import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EstimatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EstimatorBHistSourceSurface [AskSetup] [PackageSetup]
    (sample independence endpoint bias variance transport ledger provenance final : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sample ∧ UnaryHistory independence ∧ UnaryHistory bias ∧
    UnaryHistory variance ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont sample independence endpoint ∧ Cont bias variance ledger ∧
        Cont provenance ledger final ∧ PkgSig bundle final pkg

theorem EstimatorBHistSourceSurface_source_obligation [AskSetup] [PackageSetup]
    {sample independence endpoint bias variance transport ledger provenance final : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface sample independence endpoint bias variance transport ledger
        provenance final bundle pkg ->
      UnaryHistory sample ∧ UnaryHistory independence ∧ UnaryHistory endpoint ∧
        UnaryHistory bias ∧ UnaryHistory variance ∧ UnaryHistory ledger ∧
          UnaryHistory provenance ∧ UnaryHistory final ∧
            hsame endpoint (append sample independence) ∧
              hsame ledger (append bias variance) ∧
                hsame final (append provenance ledger) ∧ PkgSig bundle final pkg := by
  intro surface
  have sampleUnary : UnaryHistory sample := surface.left
  have independenceUnary : UnaryHistory independence := surface.right.left
  have biasUnary : UnaryHistory bias := surface.right.right.left
  have varianceUnary : UnaryHistory variance := surface.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    surface.right.right.right.right.right.left
  have endpointRow : Cont sample independence endpoint :=
    surface.right.right.right.right.right.right.left
  have ledgerRow : Cont bias variance ledger :=
    surface.right.right.right.right.right.right.right.left
  have finalRow : Cont provenance ledger final :=
    surface.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle final pkg :=
    surface.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sampleUnary independenceUnary endpointRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed biasUnary varianceUnary ledgerRow
  have finalUnary : UnaryHistory final :=
    unary_cont_closed provenanceUnary ledgerUnary finalRow
  exact And.intro sampleUnary
    (And.intro independenceUnary
      (And.intro endpointUnary
        (And.intro biasUnary
          (And.intro varianceUnary
            (And.intro ledgerUnary
              (And.intro provenanceUnary
                (And.intro finalUnary
                  (And.intro endpointRow
                    (And.intro ledgerRow
                      (And.intro finalRow pkgSig))))))))))

end BEDC.Derived.EstimatorUp
