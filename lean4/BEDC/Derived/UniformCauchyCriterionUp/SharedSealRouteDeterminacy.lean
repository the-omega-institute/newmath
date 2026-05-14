import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_shared_seal_route_determinacy
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqReadA
      regseqReadB realReadA realReadB sharedRouteA sharedRouteB hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqReadA ->
        Cont index tail regseqReadB ->
          Cont tail sealRow realReadA ->
            Cont tail sealRow realReadB ->
              Cont regseqReadA realReadA sharedRouteA ->
                Cont regseqReadB realReadB sharedRouteB ->
                  PkgSig bundle sharedRouteA pkg ->
                    PkgSig bundle sharedRouteB pkg ->
                      UnaryHistory regseqReadA ∧ UnaryHistory regseqReadB ∧
                        UnaryHistory realReadA ∧ UnaryHistory realReadB ∧
                          UnaryHistory sharedRouteA ∧ UnaryHistory sharedRouteB ∧
                            hsame regseqReadA regseqReadB ∧ hsame realReadA realReadB ∧
                              Cont regseqReadA realReadA sharedRouteA ∧
                                Cont regseqReadB realReadB sharedRouteB ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle sharedRouteA pkg ∧
                                      PkgSig bundle sharedRouteB pkg ∧
                                        (Cont sharedRouteA (BHist.e0 hostTail) regseqReadA ->
                                          False) ∧
                                          (Cont sharedRouteA (BHist.e1 hostTail)
                                              regseqReadA ->
                                            False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailRegseqA indexTailRegseqB tailSealRealA tailSealRealB
    regseqRealSharedA regseqRealSharedB sharedPkgA sharedPkgB
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have regseqUnaryA : UnaryHistory regseqReadA :=
    unary_cont_closed indexUnary tailUnary indexTailRegseqA
  have regseqUnaryB : UnaryHistory regseqReadB :=
    unary_cont_closed indexUnary tailUnary indexTailRegseqB
  have realUnaryA : UnaryHistory realReadA :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealA
  have realUnaryB : UnaryHistory realReadB :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealB
  have sharedUnaryA : UnaryHistory sharedRouteA :=
    unary_cont_closed regseqUnaryA realUnaryA regseqRealSharedA
  have sharedUnaryB : UnaryHistory sharedRouteB :=
    unary_cont_closed regseqUnaryB realUnaryB regseqRealSharedB
  have sameRegseq : hsame regseqReadA regseqReadB :=
    cont_respects_hsame (hsame_refl index) (hsame_refl tail) indexTailRegseqA
      indexTailRegseqB
  have sameReal : hsame realReadA realReadB :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) tailSealRealA
      tailSealRealB
  exact
    ⟨regseqUnaryA, regseqUnaryB, realUnaryA, realUnaryB, sharedUnaryA, sharedUnaryB,
      sameRegseq, sameReal, regseqRealSharedA, regseqRealSharedB, namePkg, sharedPkgA,
      sharedPkgB,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left regseqRealSharedA hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right regseqRealSharedA hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
