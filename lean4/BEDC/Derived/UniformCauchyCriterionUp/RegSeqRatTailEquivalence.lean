import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp.RegSeqRatTailEquivalence

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseqrat_tail_equivalence [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      regseqRead realRead reconstructed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont index tail regseqRead ->
          Cont tail sealRow realRead ->
            Cont tailRead realRead reconstructed ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle regseqRead pkg ->
                  PkgSig bundle realRead pkg ->
                    PkgSig bundle reconstructed pkg ->
                      hsame tailRead regseqRead ∧ UnaryHistory tailRead ∧
                        UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                          UnaryHistory reconstructed ∧ Cont index windows modulus ∧
                            Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                              Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
                                Cont tailRead realRead reconstructed ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                    PkgSig bundle regseqRead pkg ∧
                                      PkgSig bundle realRead pkg ∧
                                        PkgSig bundle reconstructed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailRead indexTailRegseq tailSealReal tailReadRealReconstructed
    tailReadPkg regseqPkg realReadPkg reconstructedPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadSameRegseq : hsame tailRead regseqRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl tail) indexTailRead indexTailRegseq
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have reconstructedUnary : UnaryHistory reconstructed :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealReconstructed
  exact
    ⟨tailReadSameRegseq, tailReadUnary, regseqUnary, realReadUnary, reconstructedUnary,
      indexWindowsModulus, modulusToleranceTail, indexTailRead, indexTailRegseq, tailSealReal,
      tailReadRealReconstructed, namePkg, tailReadPkg, regseqPkg, realReadPkg,
      reconstructedPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp.RegSeqRatTailEquivalence
