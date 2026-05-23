import BEDC.Derived.ObjectivityRefutationBoundaryUp.TasteGate

namespace BEDC.Derived.ObjectivityRefutationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObjectivityRefutationBoundaryCarrier_sibling_independence [AskSetup] [PackageSetup]
    {H K A W R T P N siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObjectivityRefutationBoundaryCarrier H K A W R T P N bundle pkg ->
      Cont T P siblingRead ->
        PkgSig bundle siblingRead pkg ->
          objectivityRefutationBoundaryFields
              (ObjectivityRefutationBoundaryUp.mk H K A W R T P N) =
            [H, K, A, W, R, T, P, N] ∧
            UnaryHistory siblingRead ∧ hsame P N ∧ PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier transport siblingPkg
  obtain ⟨_hUnary, _kUnary, _aUnary, _wUnary, _rUnary, tUnary, pUnary, _nUnary,
    _anchorRoute, _refusalRoute, _pkg, samePN⟩ := carrier
  exact ⟨rfl, unary_cont_closed tUnary pUnary transport, samePN, siblingPkg⟩

end BEDC.Derived.ObjectivityRefutationBoundaryUp
