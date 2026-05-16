import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_common_window_exhaustion [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realWindow
      diagonalWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows realWindow ->
        Cont index windows diagonalWindow ->
          PkgSig bundle realWindow pkg ->
            PkgSig bundle diagonalWindow pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory realWindow ∧
                UnaryHistory diagonalWindow ∧ Cont index windows realWindow ∧
                  Cont index windows diagonalWindow ∧ hsame realWindow diagonalWindow ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle realWindow pkg ∧
                      PkgSig bundle diagonalWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet realWindowRoute diagonalWindowRoute realWindowPkg diagonalWindowPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed indexUnary windowsUnary realWindowRoute
  have diagonalWindowUnary : UnaryHistory diagonalWindow :=
    unary_cont_closed indexUnary windowsUnary diagonalWindowRoute
  have sameWindow : hsame realWindow diagonalWindow :=
    cont_deterministic realWindowRoute diagonalWindowRoute
  exact
    ⟨indexUnary, windowsUnary, realWindowUnary, diagonalWindowUnary, realWindowRoute,
      diagonalWindowRoute, sameWindow, namePkg, realWindowPkg, diagonalWindowPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
