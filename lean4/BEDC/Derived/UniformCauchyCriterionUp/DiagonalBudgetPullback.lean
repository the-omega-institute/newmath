import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_budget_pullback [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead sealRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
        Cont diagonalRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead pullback ->
              PkgSig bundle diagonalRead pkg ->
                PkgSig bundle tailRead pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle pullback pkg ->
                      UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory pullback ∧
                          hsame modulus diagonalRead ∧ Cont index windows diagonalRead ∧
                            Cont diagonalRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                              Cont tailRead sealRead pullback ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet diagonalRoute tailReadRoute sealReadRoute pullbackRoute _diagonalPkg _tailPkg
    _sealPkg pullbackPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary diagonalRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary tailReadRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealReadRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed tailReadUnary sealReadUnary pullbackRoute
  have sameModulus : hsame modulus diagonalRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      diagonalRoute
  exact
    ⟨diagonalUnary, tailReadUnary, sealReadUnary, pullbackUnary, sameModulus,
      diagonalRoute, tailReadRoute, sealReadRoute, pullbackRoute, namePkg, pullbackPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
