import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyInterleavingPacket [AskSetup] [PackageSetup]
    (leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory leftSchedule ∧
    UnaryHistory rightSchedule ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont selector leftSchedule leftSeal ∧
        Cont selector rightSchedule rightSeal ∧ Cont leftSeal rightSeal interleavedSeal ∧
          Cont interleavedSeal modulus endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyInterleavingPacket_classifier_transport [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint leftName' rightName'
      leftSeal' rightSeal' interleavedSeal' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      hsame leftName leftName' ->
        hsame rightName rightName' ->
          Cont selector leftSchedule leftSeal' ->
            Cont selector rightSchedule rightSeal' ->
              Cont leftSeal' rightSeal' interleavedSeal' ->
                Cont interleavedSeal' modulus endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    RegularCauchyInterleavingPacket leftName' rightName' leftSchedule
                        rightSchedule selector modulus leftSeal' rightSeal' interleavedSeal'
                        transport routes provenance nameCert endpoint' bundle pkg ∧
                      hsame leftSeal leftSeal' ∧ hsame rightSeal rightSeal' ∧
                        hsame interleavedSeal interleavedSeal' ∧ hsame endpoint endpoint' := by
  intro packet sameLeftName sameRightName leftSealRoute rightSealRoute interleavedRoute
    endpointRoute endpointPkg
  obtain ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, selectorUnary,
    modulusUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, leftSealOld,
    rightSealOld, interleavedOld, endpointOld, _endpointPkg⟩ := packet
  have leftNameUnary' : UnaryHistory leftName' :=
    unary_transport leftNameUnary sameLeftName
  have rightNameUnary' : UnaryHistory rightName' :=
    unary_transport rightNameUnary sameRightName
  have leftSealUnary' : UnaryHistory leftSeal' :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary' : UnaryHistory rightSeal' :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary' : UnaryHistory interleavedSeal' :=
    unary_cont_closed leftSealUnary' rightSealUnary' interleavedRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed interleavedUnary' modulusUnary endpointRoute
  have sameLeftSeal : hsame leftSeal leftSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl leftSchedule) leftSealOld
      leftSealRoute
  have sameRightSeal : hsame rightSeal rightSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl rightSchedule) rightSealOld
      rightSealRoute
  have sameInterleaved : hsame interleavedSeal interleavedSeal' :=
    cont_respects_hsame sameLeftSeal sameRightSeal interleavedOld interleavedRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameInterleaved (hsame_refl modulus) endpointOld endpointRoute
  exact
    ⟨⟨leftNameUnary', rightNameUnary', leftScheduleUnary, rightScheduleUnary, selectorUnary,
        modulusUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary, leftSealRoute,
        rightSealRoute, interleavedRoute, endpointRoute, endpointPkg⟩,
      sameLeftSeal, sameRightSeal, sameInterleaved, sameEndpoint⟩

theorem RegularCauchyInterleavingPacket_namecert_obligations [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
            modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert
            endpoint bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
            modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert
            endpoint bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
            modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert
            endpoint bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packet (hsame_refl provenance))
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
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RegularCauchyInterleavingPacket_selector_parity_exactness [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint leftSeal' rightSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont selector leftSchedule leftSeal' ->
        Cont selector rightSchedule rightSeal' ->
          UnaryHistory leftSeal' ∧ UnaryHistory rightSeal' ∧ hsame leftSeal leftSeal' ∧
            hsame rightSeal rightSeal' := by
  intro packet leftSealRoute' rightSealRoute'
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, _modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, _interleavedRoute, _endpointRoute,
    _endpointPkg⟩ := packet
  have leftSealUnary' : UnaryHistory leftSeal' :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute'
  have rightSealUnary' : UnaryHistory rightSeal' :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute'
  have sameLeftSeal : hsame leftSeal leftSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl leftSchedule) leftSealRoute
      leftSealRoute'
  have sameRightSeal : hsame rightSeal rightSeal' :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl rightSchedule) rightSealRoute
      rightSealRoute'
  exact ⟨leftSealUnary', rightSealUnary', sameLeftSeal, sameRightSeal⟩

theorem RegularCauchyInterleavingPacket_window_seal_symmetry [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint leftSealRead rightSealRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont selector leftSchedule leftSealRead ->
        Cont selector rightSchedule rightSealRead ->
          Cont leftSealRead rightSealRead interleavedSeal ->
            Cont interleavedSeal modulus endpointRead ->
              PkgSig bundle endpointRead pkg ->
                hsame leftSeal leftSealRead ∧ hsame rightSeal rightSealRead ∧
                  hsame endpoint endpointRead ∧ UnaryHistory leftSealRead ∧
                    UnaryHistory rightSealRead ∧ UnaryHistory endpointRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro packet leftSealRoute' rightSealRoute' interleavedRoute' endpointRoute' endpointPkg'
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have sameLeftSeal : hsame leftSeal leftSealRead :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl leftSchedule) leftSealRoute
      leftSealRoute'
  have sameRightSeal : hsame rightSeal rightSealRead :=
    cont_respects_hsame (hsame_refl selector) (hsame_refl rightSchedule) rightSealRoute
      rightSealRoute'
  have interleavedSame : hsame interleavedSeal interleavedSeal :=
    cont_respects_hsame sameLeftSeal sameRightSeal interleavedRoute interleavedRoute'
  have leftSealReadUnary : UnaryHistory leftSealRead :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute'
  have rightSealReadUnary : UnaryHistory rightSealRead :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute'
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealReadUnary rightSealReadUnary interleavedRoute'
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute'
  have sameEndpoint : hsame endpoint endpointRead :=
    cont_respects_hsame interleavedSame (hsame_refl modulus) endpointRoute endpointRoute'
  exact
    ⟨sameLeftSeal, sameRightSeal, sameEndpoint, leftSealReadUnary, rightSealReadUnary,
      endpointReadUnary, endpointPkg, endpointPkg'⟩

theorem RegularCauchyInterleavingPacket_combined_modulus_exactness [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont interleavedSeal modulus endpoint' ->
        UnaryHistory modulus ∧ UnaryHistory interleavedSeal ∧ UnaryHistory endpoint' ∧
          Cont leftSeal rightSeal interleavedSeal ∧ Cont interleavedSeal modulus endpoint ∧
            Cont interleavedSeal modulus endpoint' ∧ hsame endpoint endpoint' ∧
              PkgSig bundle endpoint pkg := by
  intro packet endpointRoute'
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl interleavedSeal) (hsame_refl modulus) endpointRoute
      endpointRoute'
  exact
    ⟨modulusUnary, interleavedUnary, endpointUnary', interleavedRoute, endpointRoute,
      endpointRoute', sameEndpoint, endpointPkg⟩

theorem RegularCauchyInterleavingPacket_real_seal_non_escape [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont interleavedSeal modulus endpoint' ->
        PkgSig bundle endpoint' pkg ->
          UnaryHistory endpoint' ∧ hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg ∧
            PkgSig bundle endpoint' pkg := by
  intro packet endpointRoute' endpointPkg'
  obtain ⟨_leftNameUnary, _rightNameUnary, _leftScheduleUnary, _rightScheduleUnary,
    _selectorUnary, modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, _leftSealRoute, _rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed _selectorUnary _leftScheduleUnary _leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed _selectorUnary _rightScheduleUnary _rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl interleavedSeal) (hsame_refl modulus) endpointRoute
      endpointRoute'
  exact ⟨endpointUnary', sameEndpoint, endpointPkg, endpointPkg'⟩

theorem RegularCauchyInterleavingPacket_carrier_admission [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftName -> UnaryHistory rightName -> UnaryHistory leftSchedule ->
      UnaryHistory rightSchedule -> UnaryHistory selector -> UnaryHistory modulus ->
        UnaryHistory transport -> UnaryHistory routes -> UnaryHistory provenance ->
          UnaryHistory nameCert -> Cont selector leftSchedule leftSeal ->
            Cont selector rightSchedule rightSeal -> Cont leftSeal rightSeal interleavedSeal ->
              Cont interleavedSeal modulus endpoint -> PkgSig bundle endpoint pkg ->
                RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
                    modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert
                    endpoint bundle pkg ∧
                  UnaryHistory leftSeal ∧ UnaryHistory rightSeal ∧
                    UnaryHistory interleavedSeal ∧ UnaryHistory endpoint := by
  intro leftNameUnary rightNameUnary leftScheduleUnary rightScheduleUnary selectorUnary
    modulusUnary transportUnary routesUnary provenanceUnary nameCertUnary leftSealRoute
    rightSealRoute interleavedRoute endpointRoute endpointPkg
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedSealUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed interleavedSealUnary modulusUnary endpointRoute
  exact
    ⟨⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, selectorUnary,
        modulusUnary, transportUnary, routesUnary, provenanceUnary, nameCertUnary,
        leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute, endpointPkg⟩,
      leftSealUnary, rightSealUnary, interleavedSealUnary, endpointUnary⟩

theorem RegularCauchyInterleavingPacket_schedule_window_coverage [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint readSchedule readSeal :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont selector readSchedule readSeal ->
        (hsame leftSchedule readSchedule \/ hsame rightSchedule readSchedule) ->
          hsame leftSeal readSeal \/ hsame rightSeal readSeal := by
  intro packet readRoute scheduleSide
  obtain ⟨_leftNameUnary, _rightNameUnary, _leftScheduleUnary, _rightScheduleUnary,
    _selectorUnary, _modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, _interleavedRoute, _endpointRoute,
    _endpointPkg⟩ := packet
  cases scheduleSide with
  | inl sameLeftSchedule =>
      exact Or.inl
        (cont_respects_hsame (hsame_refl selector) sameLeftSchedule leftSealRoute
          readRoute)
  | inr sameRightSchedule =>
      exact Or.inr
        (cont_respects_hsame (hsame_refl selector) sameRightSchedule rightSealRoute
          readRoute)

theorem RegularCauchyInterleavingPacket_selector_transport_determinacy
    [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint leftSchedule' rightSchedule'
      leftSeal' rightSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      hsame leftSchedule leftSchedule' ->
        hsame rightSchedule rightSchedule' ->
          Cont selector leftSchedule' leftSeal' ->
            Cont selector rightSchedule' rightSeal' ->
              UnaryHistory leftSchedule' ∧ UnaryHistory rightSchedule' ∧
                UnaryHistory leftSeal' ∧ UnaryHistory rightSeal' ∧ hsame leftSeal leftSeal' ∧
                  hsame rightSeal rightSeal' := by
  intro packet sameLeftSchedule sameRightSchedule leftSealRoute' rightSealRoute'
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, _modulusUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, _interleavedRoute, _endpointRoute,
    _endpointPkg⟩ := packet
  have leftScheduleUnary' : UnaryHistory leftSchedule' :=
    unary_transport leftScheduleUnary sameLeftSchedule
  have rightScheduleUnary' : UnaryHistory rightSchedule' :=
    unary_transport rightScheduleUnary sameRightSchedule
  have leftSealUnary' : UnaryHistory leftSeal' :=
    unary_cont_closed selectorUnary leftScheduleUnary' leftSealRoute'
  have rightSealUnary' : UnaryHistory rightSeal' :=
    unary_cont_closed selectorUnary rightScheduleUnary' rightSealRoute'
  have sameLeftSeal : hsame leftSeal leftSeal' :=
    cont_respects_hsame (hsame_refl selector) sameLeftSchedule leftSealRoute
      leftSealRoute'
  have sameRightSeal : hsame rightSeal rightSeal' :=
    cont_respects_hsame (hsame_refl selector) sameRightSchedule rightSealRoute
      rightSealRoute'
  exact
    ⟨leftScheduleUnary', rightScheduleUnary', leftSealUnary', rightSealUnary',
      sameLeftSeal, sameRightSeal⟩

theorem RegularCauchyInterleavingPacket_public_real_seal_export [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont endpoint provenance publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory leftSchedule ∧
            UnaryHistory rightSchedule ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
              UnaryHistory leftSeal ∧ UnaryHistory rightSeal ∧ UnaryHistory interleavedSeal ∧
                UnaryHistory endpoint ∧ UnaryHistory publicRead ∧
                  Cont selector leftSchedule leftSeal ∧ Cont selector rightSchedule rightSeal ∧
                    Cont leftSeal rightSeal interleavedSeal ∧
                      Cont interleavedSeal modulus endpoint ∧
                        Cont endpoint provenance publicRead ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro packet publicRoute publicPkg
  obtain ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary provenanceUnary publicRoute
  exact
    ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, selectorUnary,
      modulusUnary, leftSealUnary, rightSealUnary, interleavedUnary, endpointUnary,
      publicReadUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
      publicRoute, endpointPkg, publicPkg⟩

theorem RegularCauchyInterleavingPacket_obligation_closure_package [AskSetup] [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint endpointRead publicRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg →
      Cont interleavedSeal modulus endpointRead →
        Cont endpointRead provenance publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory leftSeal ∧ UnaryHistory rightSeal ∧ UnaryHistory interleavedSeal ∧
              UnaryHistory endpointRead ∧ UnaryHistory publicRead ∧
                Cont leftSeal rightSeal interleavedSeal ∧
                  Cont interleavedSeal modulus endpointRead ∧
                    Cont endpointRead provenance publicRead ∧ hsame endpoint endpointRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro packet endpointReadRoute publicRoute publicPkg
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, provenanceUnary,
    _nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed interleavedUnary modulusUnary endpointReadRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary provenanceUnary publicRoute
  have sameEndpoint : hsame endpoint endpointRead :=
    cont_respects_hsame (hsame_refl interleavedSeal) (hsame_refl modulus) endpointRoute
      endpointReadRoute
  exact
    ⟨leftSealUnary, rightSealUnary, interleavedUnary, endpointReadUnary, publicReadUnary,
      interleavedRoute, endpointReadRoute, publicRoute, sameEndpoint, endpointPkg, publicPkg⟩

end BEDC.Derived.RegularCauchyInterleavingUp
