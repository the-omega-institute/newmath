import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_ledger_exactness [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      toleranceRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont modulus tolerance toleranceRead ->
          Cont thresholdRead toleranceRead tailRead ->
            PkgSig bundle thresholdRead pkg ->
              PkgSig bundle toleranceRead pkg ->
                PkgSig bundle tailRead pkg ->
                  UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory tailRead ∧ hsame modulus thresholdRead ∧
                      Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                        Cont index windows thresholdRead ∧
                          Cont modulus tolerance toleranceRead ∧
                            Cont thresholdRead toleranceRead tailRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle thresholdRead pkg ∧
                                PkgSig bundle toleranceRead pkg ∧
                                  PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold modulusToleranceRead thresholdToleranceTail
    thresholdPkg tolerancePkg tailPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed thresholdUnary toleranceReadUnary thresholdToleranceTail
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨thresholdUnary, toleranceReadUnary, tailReadUnary, sameThreshold, indexWindowsModulus,
      modulusToleranceTail, indexWindowsThreshold, modulusToleranceRead, thresholdToleranceTail,
      namePkg, thresholdPkg, tolerancePkg, tailPkg⟩

theorem UniformCauchyCriterionPacket_single_member_restriction_exactness
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name subIndex subTail
      subSealRow singletonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      hsame index subIndex ->
        hsame tail subTail ->
          hsame sealRow subSealRow ->
            Cont subIndex windows modulus ->
              Cont modulus tolerance subTail ->
                Cont subIndex subTail singletonRead ->
                  PkgSig bundle singletonRead pkg ->
                    UniformCauchyCriterionPacket subIndex windows modulus tolerance subTail
                          subSealRow transports routes provenance name bundle pkg ∧
                      UnaryHistory subIndex ∧ UnaryHistory subTail ∧
                        UnaryHistory subSealRow ∧ UnaryHistory singletonRead ∧
                          Cont subIndex windows modulus ∧ Cont modulus tolerance subTail ∧
                            Cont subIndex subTail singletonRead ∧
                              PkgSig bundle singletonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameIndex sameTail sameSealRow subIndexWindowsModulus modulusToleranceSubTail
    subIndexSubTail singletonPkg
  have restricted :
      UniformCauchyCriterionPacket subIndex windows modulus tolerance subTail subSealRow
            transports routes provenance name bundle pkg ∧
        UnaryHistory subIndex ∧ UnaryHistory subTail ∧ UnaryHistory subSealRow ∧
          Cont subIndex windows modulus ∧ Cont modulus tolerance subTail :=
    UniformCauchyCriterionPacket_subfamily_restriction packet sameIndex sameTail sameSealRow
      subIndexWindowsModulus modulusToleranceSubTail
  have singletonUnary : UnaryHistory singletonRead :=
    unary_cont_closed restricted.right.left restricted.right.right.left subIndexSubTail
  exact
    ⟨restricted.left, restricted.right.left, restricted.right.right.left,
      restricted.right.right.right.left, singletonUnary,
      restricted.right.right.right.right.left, restricted.right.right.right.right.right,
      subIndexSubTail, singletonPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
