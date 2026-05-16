import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_l10_exit_public_nonescape [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name familyRead
      sealRead publicRead l10Exit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail familyRead ->
        Cont tail sealRow sealRead ->
          Cont familyRead sealRead publicRead ->
            Cont transports routes l10Exit ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle l10Exit pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory familyRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory publicRead ∧ UnaryHistory l10Exit ∧
                          hsame provenance l10Exit ∧ Cont index windows modulus ∧
                            Cont modulus tolerance tail ∧ Cont index tail familyRead ∧
                              Cont tail sealRow sealRead ∧
                                Cont familyRead sealRead publicRead ∧
                                  Cont transports routes l10Exit ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle publicRead pkg ∧
                                        PkgSig bundle l10Exit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailFamily tailSealRead familySealPublic transportsRoutesExit publicPkg
    exitPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, transportsRoutesProvenance, namePkg⟩ :=
    packet
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed indexUnary tailUnary indexTailFamily
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed familyReadUnary sealReadUnary familySealPublic
  have l10ExitUnary : UnaryHistory l10Exit :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesExit
  have sameExit : hsame provenance l10Exit :=
    cont_deterministic transportsRoutesProvenance transportsRoutesExit
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      familyReadUnary, sealReadUnary, publicReadUnary, l10ExitUnary, sameExit,
      indexWindowsModulus, modulusToleranceTail, indexTailFamily, tailSealRead,
      familySealPublic, transportsRoutesExit, namePkg, publicPkg, exitPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
