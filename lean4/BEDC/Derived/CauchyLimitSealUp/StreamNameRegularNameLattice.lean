import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_streamname_regular_name_lattice [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      budgetRead completionRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic budgetRead ->
          Cont budgetRead diagonal completionRead ->
            Cont completionRead endpoint regularRead ->
              hsame dyadic budgetRead ->
                UnaryHistory window ∧ UnaryHistory budgetRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory regularRead ∧ hsame sealRow completionRead ∧
                    hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicBudget budgetDiagonalCompletion
    completionEndpointRegular sameDyadicBudget
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBudget
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetUnary diagonalUnary budgetDiagonalCompletion
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed completionUnary endpointUnary completionEndpointRegular
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      budgetDiagonalCompletion
  exact
    ⟨windowUnary, budgetUnary, completionUnary, regularUnary, sameSealCompletion,
      sameEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
