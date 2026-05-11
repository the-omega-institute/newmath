import BEDC.Derived.FastCauchyUp.Core

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def FastCauchyRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream modulus endpoint radius latePair transportWindow regWindow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory latePair ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      Cont stream modulus transportWindow ∧ Cont endpoint radius latePair ∧
        Cont latePair transportWindow regWindow ∧ PkgSig bundle regWindow pkg

def FastCauchyFinitePacket [AskSetup] [PackageSetup]
    (stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory latePair ∧ UnaryHistory transportWindow ∧ UnaryHistory regWindow ∧
      UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧ Cont stream modulus transportWindow ∧
        Cont endpoint radius latePair ∧ Cont latePair transportWindow regWindow ∧
          Cont regWindow sealBoundary certRow ∧ PkgSig bundle regWindow pkg

theorem FastCauchyFinitePacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
          regWindow bundle pkg ∧
        Cont stream modulus transportWindow ∧ Cont endpoint radius latePair ∧
          Cont latePair transportWindow regWindow ∧ PkgSig bundle regWindow pkg := by
  intro packet
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary,
    transportUnary, regUnary, _sealUnary, _certUnary, streamModulusRoute,
    endpointRadiusRoute, latePairTransportRoute, _certRoute, pkgRow⟩ := packet
  exact
    ⟨⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary, transportUnary,
        regUnary, streamModulusRoute, endpointRadiusRoute, latePairTransportRoute, pkgRow⟩,
      streamModulusRoute, endpointRadiusRoute, latePairTransportRoute, pkgRow⟩

theorem FastCauchyFinitePacket_precision_window_restriction [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow stream'
      modulus' endpoint' radius' latePair' transportWindow' regWindow' sealBoundary'
      certRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame endpoint endpoint' ->
            hsame radius radius' ->
              hsame sealBoundary sealBoundary' ->
                Cont stream' modulus' transportWindow' ->
                  Cont endpoint' radius' latePair' ->
                    Cont latePair' transportWindow' regWindow' ->
                      Cont regWindow' sealBoundary' certRow' ->
                        PkgSig bundle regWindow' pkg ->
                          FastCauchyFinitePacket stream' modulus' endpoint' radius' latePair'
                              transportWindow' regWindow' sealBoundary' certRow' bundle pkg ∧
                            FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius'
                              latePair' transportWindow' regWindow' bundle pkg ∧
                              hsame transportWindow transportWindow' ∧ hsame latePair latePair' ∧
                                hsame regWindow regWindow' ∧ hsame certRow certRow' := by
  intro packet sameStream sameModulus sameEndpoint sameRadius sameSeal targetTransport
    targetLatePair targetRegWindow targetCertRow targetPkg
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary,
    transportUnary, regUnary, sealUnary, _certUnary, sourceTransport, sourceLatePair,
    sourceRegWindow, sourceCertRow, _sourcePkg⟩ := packet
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have transportUnary' : UnaryHistory transportWindow' :=
    unary_cont_closed streamUnary' modulusUnary' targetTransport
  have latePairUnary' : UnaryHistory latePair' :=
    unary_cont_closed endpointUnary' radiusUnary' targetLatePair
  have regUnary' : UnaryHistory regWindow' :=
    unary_cont_closed latePairUnary' transportUnary' targetRegWindow
  have sealUnary' : UnaryHistory sealBoundary' :=
    unary_transport sealUnary sameSeal
  have certUnary' : UnaryHistory certRow' :=
    unary_cont_closed regUnary' sealUnary' targetCertRow
  have sameTransport : hsame transportWindow transportWindow' :=
    cont_respects_hsame sameStream sameModulus sourceTransport targetTransport
  have sameLatePair : hsame latePair latePair' :=
    cont_respects_hsame sameEndpoint sameRadius sourceLatePair targetLatePair
  have sameRegWindow : hsame regWindow regWindow' :=
    cont_respects_hsame sameLatePair sameTransport sourceRegWindow targetRegWindow
  have sameCertRow : hsame certRow certRow' :=
    cont_respects_hsame sameRegWindow sameSeal sourceCertRow targetCertRow
  exact
    ⟨⟨streamUnary', modulusUnary', endpointUnary', radiusUnary', latePairUnary',
        transportUnary', regUnary', sealUnary', certUnary', targetTransport, targetLatePair,
        targetRegWindow, targetCertRow, targetPkg⟩,
      ⟨streamUnary', modulusUnary', endpointUnary', radiusUnary', latePairUnary',
        transportUnary', regUnary', targetTransport, targetLatePair, targetRegWindow,
        targetPkg⟩,
      sameTransport, sameLatePair, sameRegWindow, sameCertRow⟩



end BEDC.Derived.FastCauchyUp
