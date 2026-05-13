import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_stationary_family_exhaustion [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert constantRead
      constantSeal bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont ratSeed streamWindow constantRead ->
        Cont constantRead realSeal constantSeal ->
          Cont realSeal localCert bridgeRead ->
            PkgSig bundle constantSeal pkg ->
              PkgSig bundle bridgeRead pkg ->
                hsame regseqRead constantRead ∧ hsame windowLedger constantSeal ∧
                  hsame provenance bridgeRead ∧ UnaryHistory constantRead ∧
                    UnaryHistory constantSeal ∧ UnaryHistory bridgeRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle constantSeal pkg ∧
                        PkgSig bundle bridgeRead pkg := by
  intro carrier stationaryRead stationarySeal bridgeRoute constantSealPkg bridgeReadPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, _regseqReadUnary, realSealUnary,
    _windowLedgerUnary, _provenanceUnary, localCertUnary, ratStreamRegseq,
    regseqSealLedger, sealLocalProvenance, provenancePkg⟩ := carrier
  have regseqSameConstant : hsame regseqRead constantRead :=
    cont_deterministic ratStreamRegseq stationaryRead
  have windowLedgerSameSeal : hsame windowLedger constantSeal :=
    cont_respects_hsame regseqSameConstant (hsame_refl realSeal) regseqSealLedger
      stationarySeal
  have provenanceSameBridge : hsame provenance bridgeRead :=
    cont_deterministic sealLocalProvenance bridgeRoute
  have constantReadUnary : UnaryHistory constantRead :=
    unary_cont_closed ratSeedUnary streamWindowUnary stationaryRead
  have constantSealUnary : UnaryHistory constantSeal :=
    unary_cont_closed constantReadUnary realSealUnary stationarySeal
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed realSealUnary localCertUnary bridgeRoute
  exact
    ⟨regseqSameConstant, windowLedgerSameSeal, provenanceSameBridge, constantReadUnary,
      constantSealUnary, bridgeReadUnary, provenancePkg, constantSealPkg, bridgeReadPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
