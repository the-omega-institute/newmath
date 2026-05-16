import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_tail_subfamily_pullback [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name subfamily
      tailRead sealRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      UnaryHistory subfamily →
        Cont subfamily tail tailRead →
          Cont tail sealRow sealRead →
            Cont tailRead sealRead pullback →
              PkgSig bundle pullback pkg →
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                  UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                    UnaryHistory subfamily ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory pullback ∧ Cont index windows modulus ∧
                        Cont modulus tolerance tail ∧ Cont subfamily tail tailRead ∧
                          Cont tail sealRow sealRead ∧ Cont tailRead sealRead pullback ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet subfamilyUnary subfamilyTailRead tailSealRead tailReadSealPullback pullbackPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed subfamilyUnary tailUnary subfamilyTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed tailReadUnary sealReadUnary tailReadSealPullback
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      subfamilyUnary, tailReadUnary, sealReadUnary, pullbackUnary, indexWindowsModulus,
      modulusToleranceTail, subfamilyTailRead, tailSealRead, tailReadSealPullback, namePkg,
      pullbackPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
