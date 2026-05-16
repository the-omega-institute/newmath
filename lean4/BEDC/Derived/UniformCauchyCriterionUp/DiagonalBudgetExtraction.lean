import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_budget_extraction [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead sealRead budgetRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
        Cont diagonalRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead budgetRead ->
              Cont budgetRead provenance classifierRead ->
                PkgSig bundle budgetRead pkg ->
                  UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory budgetRead ∧
                      UnaryHistory classifierRead ∧ hsame modulus diagonalRead ∧
                        Cont diagonalRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                          Cont tailRead sealRead budgetRead ∧
                            Cont budgetRead provenance classifierRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet diagonalRoute tailReadRoute sealReadRoute budgetRoute classifierRoute budgetPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, provenanceUnary, _nameUnary,
    indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary diagonalRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary tailReadRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealReadRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary budgetRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed budgetUnary provenanceUnary classifierRoute
  have sameModulus : hsame modulus diagonalRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      diagonalRoute
  exact
    ⟨diagonalUnary, tailReadUnary, sealReadUnary, budgetUnary, classifierUnary,
      sameModulus, tailReadRoute, sealReadRoute, budgetRoute, classifierRoute, namePkg,
      budgetPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
