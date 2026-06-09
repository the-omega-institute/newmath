import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DiagonalLimitCompatibilityRootTailMeetRefinementRealSealCorrespondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailMeet refinement agreement endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal tailMeet →
        Cont tailMeet dyadic refinement →
          Cont refinement realSeal agreement →
            Cont agreement cert endpoint →
              PkgSig bundle provenance pkg →
                PkgSig bundle endpoint pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row diagonal ∨ hsame row tailMeet ∨ hsame row refinement ∨
                          hsame row agreement ∨ hsame row endpoint)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont readback realSeal tailMeet ∧
                          Cont tailMeet dyadic refinement ∧
                            Cont refinement realSeal agreement ∧
                              Cont agreement cert endpoint ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg)
                      hsame ∧
                    UnaryHistory tailMeet ∧ UnaryHistory refinement ∧ UnaryHistory agreement ∧
                      UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier readbackRealTail tailMeetDyadicRefinement refinementRealAgreement
    agreementCertEndpoint provenancePkg endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _carrierProvenancePkg⟩ := carrier
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed readbackUnary realSealUnary readbackRealTail
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed tailMeetUnary dyadicUnary tailMeetDyadicRefinement
  have agreementUnary : UnaryHistory agreement :=
    unary_cont_closed refinementUnary realSealUnary refinementRealAgreement
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed agreementUnary certUnary agreementCertEndpoint
  have certRow :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row tailMeet ∨ hsame row refinement ∨
              hsame row agreement ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readback realSeal tailMeet ∧
              Cont tailMeet dyadic refinement ∧ Cont refinement realSeal agreement ∧
                Cont agreement cert endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, readbackRealTail, tailMeetDyadicRefinement, refinementRealAgreement,
          agreementCertEndpoint, provenancePkg, endpointPkg⟩
  }
  exact ⟨certRow, tailMeetUnary, refinementUnary, agreementUnary, endpointUnary⟩

theorem DiagonalLimitCompatibilityRootTailmeetRefinementRealSealCorrespondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      tailLeft tailRight tailMeet realEndpoint namedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont windows readback tailLeft →
        Cont windows readback tailRight →
          Cont tailLeft tailRight tailMeet →
            Cont tailMeet realSeal realEndpoint →
              Cont realEndpoint cert namedEndpoint →
                PkgSig bundle namedEndpoint pkg →
                  UnaryHistory tailLeft ∧ UnaryHistory tailRight ∧ UnaryHistory tailMeet ∧
                    UnaryHistory realEndpoint ∧ UnaryHistory namedEndpoint ∧
                      hsame tailLeft tailRight ∧ Cont tailMeet realSeal realEndpoint ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle namedEndpoint pkg := by
  -- BEDC touchpoint anchor: DiagonalLimitCompatibilityCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier windowsReadbackLeft windowsReadbackRight leftRightMeet meetRealEndpoint
    endpointCertNamed namedPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have tailLeftUnary : UnaryHistory tailLeft :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackLeft
  have tailRightUnary : UnaryHistory tailRight :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackRight
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed tailLeftUnary tailRightUnary leftRightMeet
  have realEndpointUnary : UnaryHistory realEndpoint :=
    unary_cont_closed tailMeetUnary realSealUnary meetRealEndpoint
  have namedEndpointUnary : UnaryHistory namedEndpoint :=
    unary_cont_closed realEndpointUnary certUnary endpointCertNamed
  have sameTails : hsame tailLeft tailRight :=
    cont_deterministic windowsReadbackLeft windowsReadbackRight
  exact
    ⟨tailLeftUnary, tailRightUnary, tailMeetUnary, realEndpointUnary, namedEndpointUnary,
      sameTails, meetRealEndpoint, provenancePkg, namedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
