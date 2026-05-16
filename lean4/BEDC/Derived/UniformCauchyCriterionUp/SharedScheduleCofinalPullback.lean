import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_schedule_cofinal_pullback
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name cofinalRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail cofinalRead ->
        Cont cofinalRead sealRow realRead ->
          PkgSig bundle cofinalRead pkg ->
            PkgSig bundle realRead pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                  UnaryHistory cofinalRead ∧ UnaryHistory realRead ∧
                    Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                      Cont index tail cofinalRead ∧ Cont cofinalRead sealRow realRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle cofinalRead pkg ∧
                          PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro packet indexTailCofinal cofinalSealReal cofinalPkg realPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed indexUnary tailUnary indexTailCofinal
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed cofinalUnary sealRowUnary cofinalSealReal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      cofinalUnary, realReadUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailCofinal, cofinalSealReal, namePkg, cofinalPkg, realPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
