import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_tail_ledger_coverage [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name emptyRead
      singletonRead pairedRead subfamilyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont BHist.Empty tail emptyRead ->
        Cont index tail singletonRead ->
          Cont singletonRead tail pairedRead ->
            Cont pairedRead tail subfamilyRead ->
              PkgSig bundle subfamilyRead pkg ->
                UnaryHistory emptyRead ∧ UnaryHistory singletonRead ∧ UnaryHistory pairedRead ∧
                  UnaryHistory subfamilyRead ∧ Cont BHist.Empty tail emptyRead ∧
                    Cont index tail singletonRead ∧ Cont singletonRead tail pairedRead ∧
                      Cont pairedRead tail subfamilyRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle subfamilyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet emptyTailRead indexTailSingleton singletonTailPaired pairedTailSubfamily
    subfamilyPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have emptyReadUnary : UnaryHistory emptyRead :=
    unary_cont_closed unary_empty tailUnary emptyTailRead
  have singletonReadUnary : UnaryHistory singletonRead :=
    unary_cont_closed indexUnary tailUnary indexTailSingleton
  have pairedReadUnary : UnaryHistory pairedRead :=
    unary_cont_closed singletonReadUnary tailUnary singletonTailPaired
  have subfamilyReadUnary : UnaryHistory subfamilyRead :=
    unary_cont_closed pairedReadUnary tailUnary pairedTailSubfamily
  exact
    ⟨emptyReadUnary, singletonReadUnary, pairedReadUnary, subfamilyReadUnary,
      emptyTailRead, indexTailSingleton, singletonTailPaired, pairedTailSubfamily, namePkg,
      subfamilyPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
