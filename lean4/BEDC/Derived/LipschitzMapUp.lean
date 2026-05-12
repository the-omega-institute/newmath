import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LipschitzMapCarrier [AskSetup] [PackageSetup]
    (source target bound graph modulus transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory bound ∧ UnaryHistory graph ∧
    UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory localCert ∧
      Cont graph bound modulus ∧ Cont modulus routes provenance ∧
        PkgSig bundle provenance pkg

theorem LipschitzMapCarrier_uniform_modulus_boundary [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont provenance localCert consumer ->
        UnaryHistory modulus ∧ UnaryHistory consumer ∧ Cont graph bound modulus ∧
          Cont modulus routes provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerCont
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed carrier.right.right.right.left carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary carrier.right.right.right.right.right.right.left consumerCont
  exact
    ⟨modulusUnary,
      consumerUnary,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.LipschitzMapUp
