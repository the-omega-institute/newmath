import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGapBoundaryTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N hostRead ->
        PkgSig bundle hostRead pkg ->
          UnaryHistory I ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory A ∧
            UnaryHistory G ∧ UnaryHistory hostRead ∧ Cont I E M ∧ Cont M B D ∧
              Cont D O A ∧ Cont G N hostRead ∧ hsame H (append A C) ∧
                PkgSig bundle P pkg ∧ PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier boundaryRoute hostPkg
  rcases carrier with
    ⟨unaryI, _unaryE, _unaryM, unaryB, unaryD, _unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, signatureRoute, branchRoute, descentRoute,
      transportSame, provenancePkg⟩
  have hostUnary : UnaryHistory hostRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  exact
    ⟨unaryI, unaryB, unaryD, unaryA, unaryG, hostUnary, signatureRoute, branchRoute,
      descentRoute, boundaryRoute, transportSame, provenancePkg, hostPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
