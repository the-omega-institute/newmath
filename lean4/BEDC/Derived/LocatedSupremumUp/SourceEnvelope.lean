import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_source_envelope [AskSetup] [PackageSetup]
    {L U A W R E H C P N sourceRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      UnaryHistory L ->
        UnaryHistory U ->
          Cont L U sourceRead ->
            Cont sourceRead A envelopeRead ->
              PkgSig bundle envelopeRead pkg ->
                UnaryHistory sourceRead ∧ UnaryHistory envelopeRead ∧ hsame L U ∧
                  Cont L U sourceRead ∧ Cont sourceRead A envelopeRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle envelopeRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier sourceUnary upperUnary sourceRoute envelopeRoute envelopePkg
  have lowerUnary : UnaryHistory A := carrier.right.left
  have hLU : hsame L U := carrier.right.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary upperUnary sourceRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceReadUnary lowerUnary envelopeRoute
  exact
    ⟨sourceReadUnary, envelopeUnary, hLU, sourceRoute, envelopeRoute, pkgSig, envelopePkg⟩

end BEDC.Derived.LocatedSupremumUp
