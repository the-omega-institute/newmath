import BEDC.Derived.UniformCauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp.NonEscapeObligation

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_window_obligation [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name toleranceRead
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tolerance toleranceRead ->
        Cont tolerance tail tailRead ->
          Cont tail sealRow sealRead ->
            PkgSig bundle toleranceRead pkg ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                        Cont modulus tolerance toleranceRead ∧ Cont tolerance tail tailRead ∧
                          Cont tail sealRow sealRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle toleranceRead pkg ∧ PkgSig bundle tailRead pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet modulusToleranceRead toleranceTailRead tailSealRead toleranceReadPkg tailReadPkg
    sealReadPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  exact
    ⟨windowsUnary, modulusUnary, toleranceUnary, toleranceReadUnary, tailReadUnary,
      sealReadUnary, indexWindowsModulus, modulusToleranceTail, modulusToleranceRead,
      toleranceTailRead, tailSealRead, namePkg, toleranceReadPkg, tailReadPkg, sealReadPkg⟩

theorem UniformCauchyCriterionPacket_shared_window_nonescape_certificate
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead realRead
      consumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow realRead ->
          Cont tailRead realRead consumer ->
            PkgSig bundle tailRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle consumer pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow
                          transports routes provenance name bundle pkg ∧
                        hsame row consumer)
                    (fun row : BHist =>
                      Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                        Cont index tail tailRead ∧ Cont tail sealRow realRead ∧
                          Cont tailRead realRead row ∧ PkgSig bundle consumer pkg)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg ∧
                        (Cont row (BHist.e0 hostTail) tailRead -> False) ∧
                          (Cont row (BHist.e1 hostTail) realRead -> False))
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet indexTailRead tailSealRealRead tailReadRealConsumer _tailReadPkg _realReadPkg
    consumerPkg
  have packetWitness :
      UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg :=
    packet
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have nonescape :=
    UniformCauchyCriterionPacket_nonescape_obligation (hostTail := hostTail) packetWitness
      indexTailRead tailSealRealRead tailReadRealConsumer consumerPkg
  obtain ⟨_indexUnaryN, _windowsUnaryN, _modulusUnaryN, _toleranceUnaryN, _tailUnaryN,
    _sealRowUnaryN, _tailReadUnaryN, _realReadUnaryN, consumerUnary, _indexWindowsModulusN,
    _modulusToleranceTailN, _indexTailReadN, _tailSealRealReadN, _tailReadRealConsumerN,
    _namePkgN, _consumerPkgN, noZero, noOne⟩ := nonescape
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer (And.intro packetWitness (hsame_refl consumer))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨indexWindowsModulus, modulusToleranceTail, indexTailRead, tailSealRealRead,
          cont_result_hsame_transport tailReadRealConsumer (hsame_symm source.right),
          consumerPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport consumerUnary (hsame_symm source.right), namePkg, consumerPkg,
          (fun hostReturn =>
            noZero
              (cont_hsame_transport source.right (hsame_refl (BHist.e0 hostTail))
                (hsame_refl tailRead) hostReturn)),
          (fun hostReturn =>
            noOne
              (cont_hsame_transport source.right (hsame_refl (BHist.e1 hostTail))
                (hsame_refl realRead) hostReturn))⟩
  }

end BEDC.Derived.UniformCauchyCriterionUp
