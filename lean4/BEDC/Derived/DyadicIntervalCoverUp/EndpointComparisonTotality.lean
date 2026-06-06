import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverEndpointComparisonTotality [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointMesh endpointRadius membershipRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U endpointMesh ->
        Cont endpointMesh M endpointRadius ->
          Cont endpointRadius V membershipRead ->
            Cont membershipRead A sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory V ∧
                  UnaryHistory endpointMesh ∧ UnaryHistory endpointRadius ∧
                    UnaryHistory membershipRead ∧ UnaryHistory sealRead ∧
                      Cont L U endpointMesh ∧ Cont endpointMesh M endpointRadius ∧
                        Cont endpointRadius V membershipRead ∧
                          Cont membershipRead A sealRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro surface endpointCont radiusCont membershipCont sealCont sealPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointMesh :=
    unary_cont_closed lUnary uUnary endpointCont
  have radiusUnary : UnaryHistory endpointRadius :=
    unary_cont_closed endpointUnary mUnary radiusCont
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed radiusUnary vUnary membershipCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed membershipUnary aUnary sealCont
  exact
    ⟨lUnary, uUnary, mUnary, vUnary, endpointUnary, radiusUnary, membershipUnary,
      sealUnary, endpointCont, radiusCont, membershipCont, sealCont, pPkg, sealPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
