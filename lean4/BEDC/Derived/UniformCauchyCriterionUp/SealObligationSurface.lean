import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_seal_obligation_package [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          PkgSig bundle regseqRead pkg ->
            PkgSig bundle realRead pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                  UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                    UnaryHistory name ∧ UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                      Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                        Cont tail sealRow transports ∧ Cont transports routes provenance ∧
                          Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg ∧
                              PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqPkg realPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, indexWindowsModulus,
    modulusToleranceTail, tailSealRowTransports, transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, regseqUnary, realUnary,
      indexWindowsModulus, modulusToleranceTail, tailSealRowTransports,
      transportsRoutesProvenance, indexTailRegseq, tailSealReal, namePkg, regseqPkg,
      realPkg⟩

theorem UniformCauchyCriterionPacket_root_seal_consumer_nonescape [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      toleranceRead tailRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont modulus tolerance toleranceRead ->
          Cont tolerance tail tailRead ->
            Cont tail sealRow realRead ->
              PkgSig bundle thresholdRead pkg ->
                PkgSig bundle toleranceRead pkg ->
                  PkgSig bundle tailRead pkg ->
                    PkgSig bundle realRead pkg ->
                      UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                          hsame modulus thresholdRead ∧ Cont index windows thresholdRead ∧
                            Cont modulus tolerance toleranceRead ∧
                              Cont tolerance tail tailRead ∧ Cont tail sealRow realRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold modulusToleranceRead toleranceTailRead tailSealReal
    _thresholdPkg _tolerancePkg _tailPkg realPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed (unary_cont_closed indexUnary windowsUnary indexWindowsModulus)
      toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨thresholdUnary, toleranceReadUnary, tailReadUnary, realUnary, sameThreshold,
      indexWindowsThreshold, modulusToleranceRead, toleranceTailRead, tailSealReal, namePkg,
      realPkg⟩

theorem UniformCauchyCriterionPacket_root_shared_tail_meet [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead rootRead sharedTailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow sealRead ->
          Cont tailRead sealRead rootRead ->
            Cont rootRead tail sharedTailRead ->
              PkgSig bundle rootRead pkg ->
                PkgSig bundle sharedTailRead pkg ->
                  UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ UnaryHistory rootRead ∧
                    UnaryHistory sharedTailRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                        Cont tail sealRow sealRead ∧ Cont tailRead sealRead rootRead ∧
                          Cont rootRead tail sharedTailRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle rootRead pkg ∧
                              PkgSig bundle sharedTailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead tailSealRoot rootTailShared rootPkg sharedPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailSealRoot
  have sharedTailUnary : UnaryHistory sharedTailRead :=
    unary_cont_closed rootReadUnary tailUnary rootTailShared
  exact
    ⟨tailReadUnary, sealReadUnary, rootReadUnary, sharedTailUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRead, tailSealRead, tailSealRoot, rootTailShared,
      namePkg, rootPkg, sharedPkg⟩

theorem UniformCauchyCriterionPacket_family_tail_intersection [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name subfamilyRead
      tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows subfamilyRead ->
        Cont subfamilyRead tail tailRead ->
          PkgSig bundle tailRead pkg ->
            UnaryHistory subfamilyRead ∧ UnaryHistory tailRead ∧
              Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                Cont index windows subfamilyRead ∧ Cont subfamilyRead tail tailRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsSubfamily subfamilyTailRead tailReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have subfamilyUnary : UnaryHistory subfamilyRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsSubfamily
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed subfamilyUnary tailUnary subfamilyTailRead
  exact
    ⟨subfamilyUnary, tailReadUnary, indexWindowsModulus, modulusToleranceTail,
      indexWindowsSubfamily, subfamilyTailRead, namePkg, tailReadPkg⟩

theorem UniformCauchyCriterionPacket_seal_route_obligation [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory sealRead ∧ Cont index windows modulus ∧
                Cont modulus tolerance tail ∧ Cont tail sealRow sealRead ∧
                  Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealRead sealReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, transportsRoutesProvenance, namePkg⟩ :=
    packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      sealReadUnary, indexWindowsModulus, modulusToleranceTail, tailSealRead,
      transportsRoutesProvenance, namePkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
