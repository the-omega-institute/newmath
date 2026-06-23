import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverFiniteMeshInduction [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N meshRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    dyadicIntervalCoverFields (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N) =
        [L, U, M, R, V, W, Q, A, H, C, P, N] ->
      UnaryHistory L -> UnaryHistory U -> UnaryHistory M -> UnaryHistory R ->
        UnaryHistory V -> UnaryHistory W -> UnaryHistory Q -> UnaryHistory A ->
          UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
            Cont M R meshRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              PkgSig bundle meshRead pkg ->
                UnaryHistory meshRead ∧ Cont M R meshRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle meshRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig UnaryHistory
  intro fields _lUnary _uUnary mUnary rUnary _vUnary _wUnary _qUnary _aUnary _hUnary
    _cUnary _pUnary _nUnary meshRoute provenancePkg namePkg meshPkg
  have _acceptedFields :
      dyadicIntervalCoverFields (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N) =
        [L, U, M, R, V, W, Q, A, H, C, P, N] := fields
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed mUnary rUnary meshRoute
  exact ⟨meshUnary, meshRoute, provenancePkg, namePkg, meshPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
