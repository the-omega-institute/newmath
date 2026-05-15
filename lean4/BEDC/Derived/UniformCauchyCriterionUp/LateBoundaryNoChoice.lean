import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_boundary_nochoice_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name familyRead
      sealRead diagonalRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail familyRead ->
        Cont tail sealRow sealRead ->
          Cont familyRead sealRead consumer ->
            Cont transports routes diagonalRead ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle diagonalRead pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory familyRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory consumer ∧ UnaryHistory diagonalRead ∧
                          hsame provenance diagonalRead ∧ Cont index windows modulus ∧
                            Cont modulus tolerance tail ∧ Cont index tail familyRead ∧
                              Cont tail sealRow sealRead ∧ Cont familyRead sealRead consumer ∧
                                Cont transports routes diagonalRead ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle consumer pkg ∧
                                    PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailFamily tailSealRead familySealConsumer transportsRoutesDiagonal
    consumerPkg diagonalPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, transportsRoutesProvenance, namePkg⟩ := packet
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed indexUnary tailUnary indexTailFamily
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed familyUnary sealReadUnary familySealConsumer
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesDiagonal
  have provenanceDiagonal : hsame provenance diagonalRead :=
    cont_deterministic transportsRoutesProvenance transportsRoutesDiagonal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      familyUnary, sealReadUnary, consumerUnary, diagonalUnary, provenanceDiagonal,
      indexWindowsModulus, modulusToleranceTail, indexTailFamily, tailSealRead,
      familySealConsumer, transportsRoutesDiagonal, namePkg, consumerPkg, diagonalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
