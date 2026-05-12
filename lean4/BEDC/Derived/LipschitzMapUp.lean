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

theorem LipschitzMapCarrier_bound_transport [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert source' target'
      bound' graph' modulus' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      hsame source source' ->
        hsame target target' ->
          hsame bound bound' ->
            hsame graph graph' ->
              Cont graph' bound' modulus' ->
                LipschitzMapCarrier source' target' bound' graph' modulus' transports routes
                    provenance localCert bundle pkg ∧
                  hsame modulus modulus' := by
  intro carrier sameSource sameTarget sameBound sameGraph modulusCont'
  obtain ⟨sourceUnary, targetUnary, boundUnary, graphUnary, transportsUnary, routesUnary,
    localCertUnary, modulusCont, provenanceCont, pkgSig⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have targetUnary' : UnaryHistory target' :=
    unary_transport targetUnary sameTarget
  have boundUnary' : UnaryHistory bound' :=
    unary_transport boundUnary sameBound
  have graphUnary' : UnaryHistory graph' :=
    unary_transport graphUnary sameGraph
  have _modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed graphUnary' boundUnary' modulusCont'
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame sameGraph sameBound modulusCont modulusCont'
  have provenanceCont' : Cont modulus' routes provenance := by
    cases sameModulus
    exact provenanceCont
  exact
    ⟨⟨sourceUnary', targetUnary', boundUnary', graphUnary', transportsUnary, routesUnary,
      localCertUnary, modulusCont', provenanceCont', pkgSig⟩, sameModulus⟩

end BEDC.Derived.LipschitzMapUp
