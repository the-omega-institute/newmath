import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_tail_filter_real_window_handoff [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      realRead filterRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow realRead →
          Cont tailRead realRead filterRead →
            Cont filterRead sealRow selectorRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle realRead pkg →
                  PkgSig bundle filterRead pkg →
                    PkgSig bundle selectorRead pkg →
                      UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                        UnaryHistory filterRead ∧ UnaryHistory selectorRead ∧
                          Cont index tail tailRead ∧ Cont tail sealRow realRead ∧
                            Cont tailRead realRead filterRead ∧
                              Cont filterRead sealRow selectorRead ∧
                                PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRealRead tailRealFilter filterSealSelector
    _tailReadPkg _realReadPkg _filterReadPkg selectorReadPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed tailReadUnary realReadUnary tailRealFilter
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed filterReadUnary sealRowUnary filterSealSelector
  exact
    ⟨tailReadUnary, realReadUnary, filterReadUnary, selectorReadUnary, indexTailRead,
      tailSealRealRead, tailRealFilter, filterSealSelector, selectorReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
