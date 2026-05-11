import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchyPacket [AskSetup] [PackageSetup]
    (stream modulus endpoint latePair transport window provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
    UnaryHistory latePair ∧ UnaryHistory transport ∧ UnaryHistory window ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont stream modulus endpoint ∧
        Cont endpoint latePair window ∧ Cont window transport provenance ∧
          PkgSig bundle provenance pkg

theorem FastCauchyPacket_modulus_transport [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow stream' modulus'
      endpoint' latePair' transport' window' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
        bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame latePair latePair' ->
            hsame transport transport' ->
              hsame nameRow nameRow' ->
                Cont stream' modulus' endpoint' ->
                  Cont endpoint' latePair' window' ->
                    Cont window' transport' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        FastCauchyPacket stream' modulus' endpoint' latePair' transport'
                            window' provenance' nameRow' bundle pkg ∧
                          hsame endpoint endpoint' ∧ hsame window window' ∧
                            hsame provenance provenance' := by
  intro packet sameStream sameModulus sameLatePair sameTransport sameNameRow
    targetEndpoint targetWindow targetProvenance targetPkg
  have streamUnary : UnaryHistory stream :=
    packet.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.left
  have latePairUnary : UnaryHistory latePair :=
    packet.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.left
  have nameRowUnary : UnaryHistory nameRow :=
    packet.right.right.right.right.right.right.right.left
  have sourceEndpoint : Cont stream modulus endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have sourceWindow : Cont endpoint latePair window :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sourceProvenance : Cont window transport provenance :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed streamUnary' modulusUnary' targetEndpoint
  have latePairUnary' : UnaryHistory latePair' :=
    unary_transport latePairUnary sameLatePair
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed endpointUnary' latePairUnary' targetWindow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed windowUnary' transportUnary' targetProvenance
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameStream sameModulus sourceEndpoint targetEndpoint
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameEndpoint sameLatePair sourceWindow targetWindow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWindow sameTransport sourceProvenance targetProvenance
  exact
    ⟨⟨streamUnary', modulusUnary', endpointUnary', latePairUnary', transportUnary',
        windowUnary', provenanceUnary', nameRowUnary', targetEndpoint, targetWindow,
        targetProvenance, targetPkg⟩,
      sameEndpoint, sameWindow, sameProvenance⟩

theorem FastCauchyPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FastCauchyPacket stream modulus endpoint latePair transport window provenance nameRow
            bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro packet (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def FastCauchyFiniteCarrier [AskSetup] [PackageSetup]
    (stream modulus endpoint latePair transport window provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
    UnaryHistory latePair ∧ UnaryHistory transport ∧ UnaryHistory window ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont stream modulus endpoint ∧
        Cont endpoint latePair transport ∧ Cont transport window provenance ∧
          Cont provenance latePair nameRow ∧ PkgSig bundle nameRow pkg

theorem FastCauchyFiniteCarrier_modulus_transport [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow stream' modulus'
      endpoint' latePair' transport' window' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
        nameRow bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame latePair latePair' ->
            hsame window window' ->
              Cont stream' modulus' endpoint' ->
                Cont endpoint' latePair' transport' ->
                  Cont transport' window' provenance' ->
                    Cont provenance' latePair' nameRow' ->
                      PkgSig bundle nameRow' pkg ->
                        FastCauchyFiniteCarrier stream' modulus' endpoint' latePair'
                            transport' window' provenance' nameRow' bundle pkg ∧
                          hsame endpoint endpoint' ∧ hsame transport transport' ∧
                            hsame provenance provenance' ∧ hsame nameRow nameRow' := by
  intro carrier sameStream sameModulus sameLatePair sameWindow endpointRow' transportRow'
    provenanceRow' nameRowRoute' pkgRow'
  have streamUnary' : UnaryHistory stream' :=
    unary_transport carrier.left sameStream
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport carrier.right.left sameModulus
  have latePairUnary' : UnaryHistory latePair' :=
    unary_transport carrier.right.right.right.left sameLatePair
  have windowUnary' : UnaryHistory window' :=
    unary_transport carrier.right.right.right.right.right.left sameWindow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed streamUnary' modulusUnary' endpointRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed endpointUnary' latePairUnary' transportRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed transportUnary' windowUnary' provenanceRow'
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_cont_closed provenanceUnary' latePairUnary' nameRowRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameStream sameModulus
      carrier.right.right.right.right.right.right.right.right.left endpointRow'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameEndpoint sameLatePair
      carrier.right.right.right.right.right.right.right.right.right.left transportRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameWindow
      carrier.right.right.right.right.right.right.right.right.right.right.left provenanceRow'
  have sameNameRow : hsame nameRow nameRow' :=
    cont_respects_hsame sameProvenance sameLatePair
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      nameRowRoute'
  exact
    ⟨⟨streamUnary', modulusUnary', endpointUnary', latePairUnary', transportUnary',
        windowUnary', provenanceUnary', nameRowUnary', endpointRow', transportRow',
        provenanceRow', nameRowRoute', pkgRow'⟩,
      sameEndpoint, sameTransport, sameProvenance, sameNameRow⟩

theorem FastCauchyFiniteCarrier_precision_window_restriction [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow stream' modulus'
      endpoint' latePair' transport' window' provenance' nameRow' precisionWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
        nameRow bundle pkg ->
      hsame stream stream' ->
        hsame modulus modulus' ->
          hsame latePair latePair' ->
            hsame window window' ->
              hsame transport' precisionWindow ->
                Cont stream' modulus' endpoint' ->
                  Cont endpoint' latePair' transport' ->
                    Cont transport' window' provenance' ->
                      Cont provenance' latePair' nameRow' ->
                        PkgSig bundle nameRow' pkg ->
                          FastCauchyFiniteCarrier stream' modulus' endpoint' latePair'
                              transport' window' provenance' nameRow' bundle pkg ∧
                            hsame transport precisionWindow ∧ hsame endpoint endpoint' ∧
                              hsame provenance provenance' := by
  intro carrier sameStream sameModulus sameLatePair sameWindow samePrecision endpointRow'
    transportRow' provenanceRow' nameRowRoute' pkgRow'
  have transported :=
    FastCauchyFiniteCarrier_modulus_transport carrier sameStream sameModulus sameLatePair
      sameWindow endpointRow' transportRow' provenanceRow' nameRowRoute' pkgRow'
  exact
    ⟨transported.left, hsame_trans transported.right.right.left samePrecision,
      transported.right.left, transported.right.right.right.left⟩

theorem FastCauchyFiniteCarrier_public_interface_export [AskSetup] [PackageSetup]
    {stream modulus endpoint latePair transport window provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
        nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
            nameRow bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
            nameRow bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          FastCauchyFiniteCarrier stream modulus endpoint latePair transport window provenance
            nameRow bundle pkg ∧ hsame row nameRow)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro carrier (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

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

theorem FastCauchyFinitePacket_obligation_closure_certificate [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary
      certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
        regWindow sealBoundary certRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          hsame ∧
        FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
          regWindow bundle pkg ∧
        UnaryHistory sealBoundary ∧ UnaryHistory certRow ∧
          Cont regWindow sealBoundary certRow := by
  intro packet
  obtain ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary,
    transportUnary, regUnary, sealUnary, certUnary, streamModulusRoute,
    endpointRadiusRoute, latePairTransportRoute, certRoute, pkgRow⟩ := packet
  have finitePacket :
      FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
        regWindow sealBoundary certRow bundle pkg :=
    ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary, transportUnary,
      regUnary, sealUnary, certUnary, streamModulusRoute, endpointRadiusRoute,
      latePairTransportRoute, certRoute, pkgRow⟩
  have regseqWindow :
      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
        regWindow bundle pkg :=
    ⟨streamUnary, modulusUnary, endpointUnary, radiusUnary, latePairUnary, transportUnary,
      regUnary, streamModulusRoute, endpointRadiusRoute, latePairTransportRoute, pkgRow⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          (fun row : BHist =>
            FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow
              regWindow sealBoundary certRow bundle pkg ∧
                (hsame row regWindow ∨ hsame row sealBoundary ∨ hsame row certRow))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regWindow (And.intro finitePacket (Or.inl (hsame_refl regWindow)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameReg =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameReg)
          | inr sourceRows =>
              cases sourceRows with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))
              | inr sameCert =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCert))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, regseqWindow, sealUnary, certUnary, certRoute⟩

theorem FastCauchyFinitePacket_shared_window_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      stream' modulus' endpoint' radius' latePair' transportWindow' regWindow'
      sealBoundary' certRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      FastCauchyFinitePacket stream' modulus' endpoint' radius' latePair' transportWindow'
          regWindow' sealBoundary' certRow' bundle pkg ->
        hsame stream stream' ->
          hsame modulus modulus' ->
            hsame endpoint endpoint' ->
              hsame radius radius' ->
                hsame latePair latePair' ->
                  SemanticNameCert
                    (fun row : BHist =>
                      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair
                          transportWindow regWindow bundle pkg ∧
                        FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius' latePair'
                          transportWindow' regWindow' bundle pkg ∧
                        hsame transportWindow transportWindow' ∧
                        hsame regWindow regWindow' ∧
                        (hsame row transportWindow ∨ hsame row transportWindow' ∨
                          hsame row regWindow ∨ hsame row regWindow'))
                    (fun row : BHist =>
                      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair
                          transportWindow regWindow bundle pkg ∧
                        FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius' latePair'
                          transportWindow' regWindow' bundle pkg ∧
                        hsame transportWindow transportWindow' ∧
                        hsame regWindow regWindow' ∧
                        (hsame row transportWindow ∨ hsame row transportWindow' ∨
                          hsame row regWindow ∨ hsame row regWindow'))
                    (fun row : BHist =>
                      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair
                          transportWindow regWindow bundle pkg ∧
                        FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius' latePair'
                          transportWindow' regWindow' bundle pkg ∧
                        hsame transportWindow transportWindow' ∧
                        hsame regWindow regWindow' ∧
                        (hsame row transportWindow ∨ hsame row transportWindow' ∨
                          hsame row regWindow ∨ hsame row regWindow'))
                    hsame := by
  intro packet packet' sameStream sameModulus _sameEndpoint _sameRadius sameLatePair
  have regseqWindow :
      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
        regWindow bundle pkg :=
    (FastCauchyFinitePacket_regseqrat_handoff packet).left
  have regseqWindow' :
      FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius' latePair'
        transportWindow' regWindow' bundle pkg :=
    (FastCauchyFinitePacket_regseqrat_handoff packet').left
  have sameTransportWindow : hsame transportWindow transportWindow' :=
    cont_respects_hsame sameStream sameModulus
      packet.right.right.right.right.right.right.right.right.right.left
      packet'.right.right.right.right.right.right.right.right.right.left
  have sameRegWindow : hsame regWindow regWindow' :=
    cont_respects_hsame sameLatePair sameTransportWindow
      packet.right.right.right.right.right.right.right.right.right.right.right.left
      packet'.right.right.right.right.right.right.right.right.right.right.right.left
  have sourceAtTransport :
      FastCauchyRegSeqRatWindow stream modulus endpoint radius latePair transportWindow
          regWindow bundle pkg ∧
        FastCauchyRegSeqRatWindow stream' modulus' endpoint' radius' latePair'
          transportWindow' regWindow' bundle pkg ∧
        hsame transportWindow transportWindow' ∧ hsame regWindow regWindow' ∧
          (hsame transportWindow transportWindow ∨ hsame transportWindow transportWindow' ∨
            hsame transportWindow regWindow ∨ hsame transportWindow regWindow') :=
    ⟨regseqWindow, regseqWindow', sameTransportWindow, sameRegWindow,
      Or.inl (hsame_refl transportWindow)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro transportWindow sourceAtTransport
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        refine ⟨source.left, source.right.left, source.right.right.left,
          source.right.right.right.left, ?_⟩
        cases source.right.right.right.right with
        | inl sameTransport =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTransport)
        | inr rest =>
            cases rest with
            | inl sameTransport' =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTransport'))
            | inr rest' =>
                cases rest' with
                | inl sameReg =>
                    exact Or.inr (Or.inr (Or.inl
                      (hsame_trans (hsame_symm sameRows) sameReg)))
                | inr sameReg' =>
                    exact Or.inr (Or.inr (Or.inr
                      (hsame_trans (hsame_symm sameRows) sameReg')))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
theorem FastCauchyFinitePacket_dyadicprecision_window_cofinality [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      precision selectedThreshold selectedEndpoint selectedLatePair selectedWindow
      selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory precision ->
        Cont modulus precision selectedThreshold ->
          Cont endpoint precision selectedEndpoint ->
            Cont latePair precision selectedLatePair ->
              Cont selectedThreshold selectedEndpoint selectedWindow ->
                Cont selectedLatePair selectedWindow selectedRead ->
                  PkgSig bundle selectedRead pkg ->
                    UnaryHistory selectedThreshold ∧ UnaryHistory selectedEndpoint ∧
                      UnaryHistory selectedLatePair ∧ UnaryHistory selectedWindow ∧
                        UnaryHistory selectedRead ∧ Cont modulus precision selectedThreshold ∧
                          Cont endpoint precision selectedEndpoint ∧
                            Cont latePair precision selectedLatePair ∧
                              Cont selectedThreshold selectedEndpoint selectedWindow ∧
                                Cont selectedLatePair selectedWindow selectedRead ∧
                                  PkgSig bundle selectedRead pkg := by
  intro packet precisionUnary thresholdRow endpointRow latePairRow windowRow readRow pkgRow
  obtain ⟨_streamUnary, modulusUnary, endpointUnary, _radiusUnary, latePairUnary,
    _transportUnary, _regUnary, _sealUnary, _certUnary, _streamModulusRoute,
    _endpointRadiusRoute, _latePairTransportRoute, _certRoute, _packetPkg⟩ := packet
  have thresholdUnary : UnaryHistory selectedThreshold :=
    unary_cont_closed modulusUnary precisionUnary thresholdRow
  have endpointSelectedUnary : UnaryHistory selectedEndpoint :=
    unary_cont_closed endpointUnary precisionUnary endpointRow
  have latePairSelectedUnary : UnaryHistory selectedLatePair :=
    unary_cont_closed latePairUnary precisionUnary latePairRow
  have windowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed thresholdUnary endpointSelectedUnary windowRow
  have readUnary : UnaryHistory selectedRead :=
    unary_cont_closed latePairSelectedUnary windowUnary readRow
  exact
    ⟨thresholdUnary, endpointSelectedUnary, latePairSelectedUnary, windowUnary, readUnary,
      thresholdRow, endpointRow, latePairRow, windowRow, readRow, pkgRow⟩

end BEDC.Derived.FastCauchyUp
