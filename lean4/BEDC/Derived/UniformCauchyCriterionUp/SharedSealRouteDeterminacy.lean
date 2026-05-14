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

theorem UniformCauchyCriterionPacket_finite_family_seal_overlap_determinacy [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead sharedRoute overlapRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead sharedRoute ->
            Cont sharedRoute transports overlapRead ->
              PkgSig bundle regseqRead pkg ->
                PkgSig bundle realRead pkg ->
                  PkgSig bundle sharedRoute pkg ->
                    PkgSig bundle overlapRead pkg ->
                      UnaryHistory overlapRead ∧ Cont regseqRead realRead sharedRoute ∧
                        Cont sharedRoute transports overlapRead ∧
                          PkgSig bundle overlapRead pkg ∧
                            (Cont overlapRead (BHist.e0 hostTail) regseqRead -> False) ∧
                              (Cont overlapRead (BHist.e1 hostTail) realRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealShared sharedTransportsOverlap
    _regseqPkg _realPkg _sharedPkg overlapPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have sharedUnary : UnaryHistory sharedRoute :=
    unary_cont_closed regseqUnary realUnary regseqRealShared
  have overlapUnary : UnaryHistory overlapRead :=
    unary_cont_closed sharedUnary transportsUnary sharedTransportsOverlap
  exact
    ⟨overlapUnary, regseqRealShared, sharedTransportsOverlap, overlapPkg,
      (fun backToRegseq =>
        cont_triangle_cycle_right_zero_tail_absurd regseqRealShared
          sharedTransportsOverlap backToRegseq),
      (fun backToReal =>
        let sameSharedComm : hsame sharedRoute (append realRead regseqRead) :=
          unary_cont_comm regseqUnary realUnary regseqRealShared
            (cont_intro (h := realRead) (k := regseqRead) rfl)
        let realRegseqShared : Cont realRead regseqRead sharedRoute :=
          cont_result_hsame_transport
            (cont_intro (h := realRead) (k := regseqRead) rfl)
            (hsame_symm sameSharedComm)
        cont_triangle_cycle_right_visible_tail_absurd realRegseqShared
          sharedTransportsOverlap backToReal)⟩

end BEDC.Derived.UniformCauchyCriterionUp
