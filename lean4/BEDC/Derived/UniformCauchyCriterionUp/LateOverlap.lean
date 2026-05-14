import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_overlap_exhaustion [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name familyRead
      sealRead transportedRead consumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail familyRead →
        Cont tail sealRow sealRead →
          Cont transports routes transportedRead →
            Cont familyRead sealRead consumer →
              PkgSig bundle familyRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle consumer pkg →
                    UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                      UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                        UnaryHistory transportedRead ∧ UnaryHistory consumer ∧
                          hsame provenance transportedRead ∧ Cont index windows modulus ∧
                            Cont modulus tolerance tail ∧ Cont transports routes
                              transportedRead ∧ Cont familyRead sealRead consumer ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg ∧
                                (Cont consumer (BHist.e0 hostTail) familyRead → False) ∧
                                  (Cont consumer (BHist.e1 hostTail) familyRead →
                                    False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailFamily tailSealRead transportsRoutesRead familySealConsumer
    _familyPkg _sealPkg consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, transportsRoutesProvenance, namePkg⟩ :=
      packet
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesRead
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed indexUnary tailUnary indexTailFamily
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed familyUnary sealReadUnary familySealConsumer
  have sameProvenanceTransported : hsame provenance transportedRead :=
    cont_deterministic transportsRoutesProvenance transportsRoutesRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      transportedUnary, consumerUnary, sameProvenanceTransported, indexWindowsModulus,
      modulusToleranceTail, transportsRoutesRead, familySealConsumer, namePkg, consumerPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left familySealConsumer hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right familySealConsumer hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
