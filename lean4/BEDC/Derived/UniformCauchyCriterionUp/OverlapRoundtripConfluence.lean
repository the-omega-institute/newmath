import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_overlap_roundtrip_confluence [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name refinedA
      refinedB sealReadA sealReadB rootA rootB endpointA endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows refinedA ->
        Cont index windows refinedB ->
          Cont tail sealRow sealReadA ->
            Cont tail sealRow sealReadB ->
              Cont refinedA sealReadA rootA ->
                Cont refinedB sealReadB rootB ->
                  Cont rootA name endpointA ->
                    Cont rootB name endpointB ->
                      PkgSig bundle endpointA pkg ->
                        PkgSig bundle endpointB pkg ->
                          UnaryHistory rootA ∧ UnaryHistory rootB ∧
                            UnaryHistory endpointA ∧ UnaryHistory endpointB ∧
                              hsame refinedA refinedB ∧ hsame sealReadA sealReadB ∧
                                hsame rootA rootB ∧ hsame endpointA endpointB ∧
                                  Cont rootA name endpointA ∧ Cont rootB name endpointB ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle endpointA pkg ∧
                                      PkgSig bundle endpointB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsRefinedA indexWindowsRefinedB tailSealReadA tailSealReadB
    refinedSealRootA refinedSealRootB rootNameEndpointA rootNameEndpointB endpointPkgA
    endpointPkgB
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have refinedUnaryA : UnaryHistory refinedA :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRefinedA
  have refinedUnaryB : UnaryHistory refinedB :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRefinedB
  have sealReadUnaryA : UnaryHistory sealReadA :=
    unary_cont_closed tailUnary sealRowUnary tailSealReadA
  have sealReadUnaryB : UnaryHistory sealReadB :=
    unary_cont_closed tailUnary sealRowUnary tailSealReadB
  have rootUnaryA : UnaryHistory rootA :=
    unary_cont_closed refinedUnaryA sealReadUnaryA refinedSealRootA
  have rootUnaryB : UnaryHistory rootB :=
    unary_cont_closed refinedUnaryB sealReadUnaryB refinedSealRootB
  have endpointUnaryA : UnaryHistory endpointA :=
    unary_cont_closed rootUnaryA nameUnary rootNameEndpointA
  have endpointUnaryB : UnaryHistory endpointB :=
    unary_cont_closed rootUnaryB nameUnary rootNameEndpointB
  have refinedSame : hsame refinedA refinedB :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsRefinedA
      indexWindowsRefinedB
  have sealReadSame : hsame sealReadA sealReadB :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) tailSealReadA tailSealReadB
  have rootSame : hsame rootA rootB :=
    cont_respects_hsame refinedSame sealReadSame refinedSealRootA refinedSealRootB
  have endpointSame : hsame endpointA endpointB :=
    cont_respects_hsame rootSame (hsame_refl name) rootNameEndpointA rootNameEndpointB
  exact
    ⟨rootUnaryA, rootUnaryB, endpointUnaryA, endpointUnaryB, refinedSame, sealReadSame,
      rootSame, endpointSame, rootNameEndpointA, rootNameEndpointB, namePkg, endpointPkgA,
      endpointPkgB⟩

end BEDC.Derived.UniformCauchyCriterionUp
