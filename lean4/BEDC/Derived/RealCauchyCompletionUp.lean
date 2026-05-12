import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCauchyCompletionCarrier [AskSetup] [PackageSetup]
    (stream modulus diagonal sealRow provenance : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont stream modulus diagonal ∧
      Cont diagonal sealRow provenance ∧ PkgSig bundle provenance pkg

theorem RealCauchyCompletionCarrier_transport_stability [AskSetup] [PackageSetup]
    {stream modulus diagonal sealRow provenance stream' modulus' diagonal' sealRow'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier stream modulus diagonal sealRow provenance bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame sealRow sealRow' ->
            hsame provenance provenance' ->
              Cont stream' modulus' diagonal' ->
                Cont diagonal' sealRow' provenance' ->
                  RealCauchyCompletionCarrier stream' modulus' diagonal' sealRow' provenance'
                      bundle pkg ∧
                    hsame diagonal diagonal' := by
  intro carrier sameStream sameModulus sameSeal sameProvenance
  intro streamModulusDiagonal' diagonalSealProvenance'
  obtain ⟨streamUnary, modulusUnary, diagonalUnary, sealUnary, provenanceUnary,
    streamModulusDiagonal, diagonalSealProvenance, provenancePkg⟩ := carrier
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameStream sameModulus streamModulusDiagonal streamModulusDiagonal'
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  cases sameProvenance
  exact
    ⟨⟨streamUnary', modulusUnary', diagonalUnary', sealUnary', provenanceUnary',
        streamModulusDiagonal', diagonalSealProvenance', provenancePkg⟩,
      sameDiagonal⟩

end BEDC.Derived.RealCauchyCompletionUp
