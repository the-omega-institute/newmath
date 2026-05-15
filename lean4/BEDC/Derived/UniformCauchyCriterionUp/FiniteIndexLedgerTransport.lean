import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_index_ledger_transport [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name index'
      familyRead thresholdRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      hsame index index' ->
        Cont index' windows familyRead ->
          Cont familyRead modulus thresholdRead ->
            Cont thresholdRead tolerance tailRead ->
              Cont tailRead sealRow sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory index' ∧ UnaryHistory familyRead ∧
                    UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory sealRead ∧ Cont index' windows familyRead ∧
                        Cont familyRead modulus thresholdRead ∧
                          Cont thresholdRead tolerance tailRead ∧
                            Cont tailRead sealRow sealRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro packet sameIndex indexWindowFamily familyModulusThreshold thresholdToleranceTail
    tailSealRead sealReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have indexUnary' : UnaryHistory index' :=
    unary_transport indexUnary sameIndex
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed indexUnary' windowsUnary indexWindowFamily
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed familyUnary modulusUnary familyModulusThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed thresholdUnary toleranceUnary thresholdToleranceTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary sealRowUnary tailSealRead
  exact
    ⟨indexUnary', familyUnary, thresholdUnary, tailReadUnary, sealReadUnary,
      indexWindowFamily, familyModulusThreshold, thresholdToleranceTail, tailSealRead,
      namePkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
