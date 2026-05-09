import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EnrichedCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EnrichedCatCertificateSurface [AskSetup] [PackageSetup]
    (category monoidal hom identity transport provenance readback endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
    UnaryHistory identity ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont hom identity (append hom identity) ∧
        Cont (append hom identity) transport readback ∧
          Cont provenance readback endpoint ∧ PkgSig bundle endpoint pkg

theorem EnrichedCatCertificateSurface_source_obligation [AskSetup] [PackageSetup]
    {category monoidal hom identity transport provenance readback endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatCertificateSurface category monoidal hom identity transport provenance
        readback endpoint bundle pkg ->
      UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
        UnaryHistory identity ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
          Cont provenance readback endpoint ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have homUnary : UnaryHistory hom := surface.right.right.left
  have identityUnary : UnaryHistory identity := surface.right.right.right.left
  have transportUnary : UnaryHistory transport := surface.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := surface.right.right.right.right.right.left
  have homIdentityUnary : UnaryHistory (append hom identity) :=
    unary_cont_closed homUnary identityUnary surface.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed homIdentityUnary transportUnary
      surface.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary readbackUnary
      surface.right.right.right.right.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro homUnary
        (And.intro identityUnary
          (And.intro readbackUnary
            (And.intro endpointUnary
              (And.intro surface.right.right.right.right.right.right.right.right.left
                surface.right.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.EnrichedCatUp
