import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_root_l10_sibling_route_certificate
    [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint
      streamWindow regseqRead realRead routeRead : BHist}
    {carrierBundle routeBundle : ProbeBundle ProbeName} {carrierPkg routePkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint carrierBundle carrierPkg ->
      Cont schedule source streamWindow ->
        Cont streamWindow dyadic regseqRead ->
          Cont regseqRead diagonal realRead ->
            Cont realRead endpoint routeRead ->
              hsame dyadic regseqRead ->
                PkgSig routeBundle routeRead routePkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row routeRead ∧ Cont schedule source streamWindow ∧
                        Cont streamWindow dyadic regseqRead ∧
                          Cont regseqRead diagonal realRead ∧
                            Cont realRead endpoint routeRead)
                    (fun row : BHist =>
                      hsame row routeRead ∧ PkgSig routeBundle routeRead routePkg)
                    hsame ∧ hsame sealRow realRead ∧
                      hsame endpoint (append provenance localCert) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier scheduleSourceWindow windowDyadicRead readDiagonalReal
    realEndpointRoute sameDyadicRead routePkgSig
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary dyadicUnary windowDyadicRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary diagonalUnary readDiagonalReal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed realReadUnary endpointUnary realEndpointRoute
  have sameSealReal : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicRead (hsame_refl diagonal) dyadicDiagonalSeal
      readDiagonalReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row routeRead ∧ Cont schedule source streamWindow ∧
            Cont streamWindow dyadic regseqRead ∧ Cont regseqRead diagonal realRead ∧
              Cont realRead endpoint routeRead)
        (fun row : BHist => hsame row routeRead ∧ PkgSig routeBundle routeRead routePkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routeRead (And.intro (hsame_refl routeRead) routeReadUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, scheduleSourceWindow, windowDyadicRead, readDiagonalReal,
            realEndpointRoute⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left routePkgSig
    }
  exact ⟨cert, sameSealReal, sameEndpoint⟩

end BEDC.Derived.CauchyLimitSealUp
