import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_root_tailmeet_refinement_real_seal_correspondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailEntry refinementRead agreementSeal endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows tailEntry →
        Cont tailEntry sealRow refinementRead →
          Cont refinementRead realSeal agreementSeal →
            Cont agreementSeal cert endpoint →
              PkgSig bundle endpoint pkg →
                UnaryHistory tailEntry ∧ UnaryHistory refinementRead ∧
                  UnaryHistory agreementSeal ∧ UnaryHistory endpoint ∧
                    Cont dyadic windows tailEntry ∧ Cont tailEntry sealRow refinementRead ∧
                      Cont refinementRead realSeal agreementSeal ∧
                        Cont agreementSeal cert endpoint ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsTail tailSealRefinement refinementRealAgreement
    agreementCertEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailEntryUnary : UnaryHistory tailEntry :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsTail
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed tailEntryUnary sealRowUnary tailSealRefinement
  have agreementSealUnary : UnaryHistory agreementSeal :=
    unary_cont_closed refinementReadUnary realSealUnary refinementRealAgreement
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed agreementSealUnary certUnary agreementCertEndpoint
  exact
    ⟨tailEntryUnary, refinementReadUnary, agreementSealUnary, endpointUnary,
      dyadicWindowsTail, tailSealRefinement, refinementRealAgreement, agreementCertEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
