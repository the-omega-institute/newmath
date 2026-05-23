import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyNegationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyNegationCarrier [AskSetup] [PackageSetup]
    (source window dyadic classifier flipped sealRow transportRow route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory classifier ∧ UnaryHistory flipped ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source window dyadic ∧ Cont dyadic classifier flipped ∧
          Cont flipped sealRow transportRow ∧ Cont transportRow route provenance ∧
            Cont sealRow provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem RegularCauchyNegationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
            transportRow route provenance name bundle pkg ∧ hsame row sealRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem RegularCauchyNegationCarrier_diagonal_limit_readout [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      diagonalRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont window dyadic diagonalRead ->
        Cont classifier flipped limitRead ->
          PkgSig bundle diagonalRead pkg ->
            PkgSig bundle limitRead pkg ->
              UnaryHistory diagonalRead ∧ UnaryHistory limitRead ∧
                Cont source window dyadic ∧ Cont dyadic classifier flipped ∧
                  Cont window dyadic diagonalRead ∧ Cont classifier flipped limitRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg ∧
                      PkgSig bundle limitRead pkg := by
  intro carrier windowDyadicRead classifierFlippedRead diagonalReadPkg limitReadPkg
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceWindowDyadic, dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRead
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed classifierUnary flippedUnary classifierFlippedRead
  exact
    ⟨diagonalReadUnary, limitReadUnary, sourceWindowDyadic, dyadicClassifierFlipped,
      windowDyadicRead, classifierFlippedRead, provenancePkg, diagonalReadPkg, limitReadPkg⟩

theorem RegularCauchyNegationCarrier_public_seal_export [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      realBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg →
      Cont name route realBoundary →
        PkgSig bundle realBoundary pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              (fun row : BHist =>
                RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
                    transportRow route provenance name bundle pkg ∧ hsame row sealRow)
              hsame ∧
            UnaryHistory sealRow ∧
            UnaryHistory name ∧
            UnaryHistory realBoundary ∧
            Cont sealRow provenance name ∧
            Cont name route realBoundary ∧
            PkgSig bundle name pkg ∧
            PkgSig bundle realBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier nameRouteBoundary boundaryPkg
  have cert :=
    RegularCauchyNegationCarrier_namecert_obligations carrier
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, _classifierUnary, _flippedUnary,
    sealUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _sourceWindowDyadic, _dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, sealProvenanceName, _provenancePkg, namePkg⟩ := carrier
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed nameUnary routeUnary nameRouteBoundary
  exact
    ⟨cert, sealUnary, nameUnary, boundaryUnary, sealProvenanceName, nameRouteBoundary, namePkg,
      boundaryPkg⟩

theorem RegularCauchyNegationCarrier_bridge_readback_scope [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont name route bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory classifier ∧ UnaryHistory flipped ∧ UnaryHistory sealRow ∧
              UnaryHistory bridgeRead ∧ Cont source window dyadic ∧
                Cont dyadic classifier flipped ∧ Cont flipped sealRow transportRow ∧
                  Cont transportRow route provenance ∧ Cont sealRow provenance name ∧
                    Cont name route bridgeRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier nameRouteBridge bridgePkg
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary,
    sealUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
    sourceWindowDyadic, dyadicClassifierFlipped, flippedSealTransport,
    transportRouteProvenance, sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed nameUnary routeUnary nameRouteBridge
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary, sealUnary,
      bridgeUnary, sourceWindowDyadic, dyadicClassifierFlipped, flippedSealTransport,
      transportRouteProvenance, sealProvenanceName, nameRouteBridge, provenancePkg,
      bridgePkg⟩

theorem RegularCauchyNegationCarrier_algebraic_handoff [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name sumRead
      diffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont flipped classifier sumRead ->
        Cont flipped dyadic diffRead ->
          PkgSig bundle sumRead pkg ->
            PkgSig bundle diffRead pkg ->
              UnaryHistory flipped ∧ UnaryHistory classifier ∧ UnaryHistory dyadic ∧
                UnaryHistory sealRow ∧ UnaryHistory sumRead ∧ UnaryHistory diffRead ∧
                  Cont dyadic classifier flipped ∧ Cont flipped sealRow transportRow ∧
                    Cont flipped classifier sumRead ∧ Cont flipped dyadic diffRead ∧
                      PkgSig bundle sumRead pkg ∧ PkgSig bundle diffRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier flippedClassifierSum flippedDyadicDiff sumPkg diffPkg
  obtain ⟨_sourceUnary, _windowUnary, dyadicUnary, classifierUnary, flippedUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _sourceWindowDyadic, dyadicClassifierFlipped, flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, _provenancePkg, _namePkg⟩ := carrier
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed flippedUnary classifierUnary flippedClassifierSum
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed flippedUnary dyadicUnary flippedDyadicDiff
  exact
    ⟨flippedUnary, classifierUnary, dyadicUnary, sealUnary, sumUnary, diffUnary,
      dyadicClassifierFlipped, flippedSealTransport, flippedClassifierSum, flippedDyadicDiff,
      sumPkg, diffPkg⟩

theorem RegularCauchyNegationCarrier_involutive_seal_boundary [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      secondFlip finalBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont flipped dyadic secondFlip ->
        Cont secondFlip sealRow finalBoundary ->
          PkgSig bundle secondFlip pkg ->
            PkgSig bundle finalBoundary pkg ->
              UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                UnaryHistory classifier ∧ UnaryHistory flipped ∧ UnaryHistory secondFlip ∧
                  UnaryHistory finalBoundary ∧ Cont source window dyadic ∧
                    Cont dyadic classifier flipped ∧ Cont flipped dyadic secondFlip ∧
                      Cont secondFlip sealRow finalBoundary ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle secondFlip pkg ∧ PkgSig bundle finalBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier flippedDyadicSecond secondSealBoundary secondPkg boundaryPkg
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, sourceWindowDyadic,
    dyadicClassifierFlipped, _flippedSealTransport, _transportRouteProvenance,
    _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have secondUnary : UnaryHistory secondFlip :=
    unary_cont_closed flippedUnary dyadicUnary flippedDyadicSecond
  have boundaryUnary : UnaryHistory finalBoundary :=
    unary_cont_closed secondUnary sealUnary secondSealBoundary
  exact
    ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary, secondUnary,
      boundaryUnary, sourceWindowDyadic, dyadicClassifierFlipped, flippedDyadicSecond,
      secondSealBoundary, provenancePkg, secondPkg, boundaryPkg⟩

theorem RegularCauchyNegationCarrier_transport [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      source' window' dyadic' classifier' flipped' sealRow' transportRow' route'
      provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg →
      hsame source source' →
        hsame window window' →
          hsame dyadic dyadic' →
            hsame classifier classifier' →
              hsame flipped flipped' →
                hsame sealRow sealRow' →
                  hsame transportRow transportRow' →
                    hsame route route' →
                      hsame provenance provenance' →
                        hsame name name' →
                          RegularCauchyNegationCarrier source' window' dyadic'
                            classifier' flipped' sealRow' transportRow' route' provenance' name'
                            bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier sameSource sameWindow sameDyadic sameClassifier sameFlipped sameSeal
    sameTransport sameRoute sameProvenance sameName
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, classifierUnary, flippedUnary, sealUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, sourceWindowDyadic,
    dyadicClassifierFlipped, flippedSealTransport, transportRouteProvenance,
    sealProvenanceName, provenancePkg, namePkg⟩ := carrier
  cases sameSource
  cases sameWindow
  cases sameDyadic
  cases sameClassifier
  cases sameFlipped
  cases sameSeal
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameName
  exact
    ⟨unary_transport sourceUnary (hsame_refl source), unary_transport windowUnary
        (hsame_refl window), unary_transport dyadicUnary (hsame_refl dyadic),
      unary_transport classifierUnary (hsame_refl classifier),
      unary_transport flippedUnary (hsame_refl flipped),
      unary_transport sealUnary (hsame_refl sealRow),
      unary_transport transportUnary (hsame_refl transportRow),
      unary_transport routeUnary (hsame_refl route),
      unary_transport provenanceUnary (hsame_refl provenance),
       unary_transport nameUnary (hsame_refl name), sourceWindowDyadic, dyadicClassifierFlipped,
       flippedSealTransport, transportRouteProvenance, sealProvenanceName, provenancePkg, namePkg⟩

theorem RegularCauchyNegationCarrier_sign_flip_ledger_stability [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      signRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont dyadic classifier flipped ->
        Cont flipped sealRow transportRow ->
          Cont flipped classifier signRead ->
            PkgSig bundle signRead pkg ->
              UnaryHistory dyadic ∧ UnaryHistory classifier ∧ UnaryHistory flipped ∧
                UnaryHistory signRead ∧ Cont source window dyadic ∧
                  Cont dyadic classifier flipped ∧ Cont flipped sealRow transportRow ∧
                    Cont flipped classifier signRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle signRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier dyadicClassifierFlipped' flippedSealTransport' flippedClassifierSign signPkg
  obtain ⟨_sourceUnary, _windowUnary, dyadicUnary, classifierUnary, flippedUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceWindowDyadic, _dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have signUnary : UnaryHistory signRead :=
    unary_cont_closed flippedUnary classifierUnary flippedClassifierSign
  exact
    ⟨dyadicUnary, classifierUnary, flippedUnary, signUnary, sourceWindowDyadic,
      dyadicClassifierFlipped', flippedSealTransport', flippedClassifierSign, provenancePkg,
      signPkg⟩

theorem RegularCauchyNegationCarrier_real_algebra_bridge_certificate [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      algebraRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg →
      Cont flipped classifier algebraRead →
        Cont name route bridgeRead →
          PkgSig bundle algebraRead pkg →
            PkgSig bundle bridgeRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row bridgeRead ∧
                      RegularCauchyNegationCarrier source window dyadic classifier flipped
                        sealRow transportRow route provenance name bundle pkg)
                  (fun row : BHist =>
                    hsame row bridgeRead ∧ Cont flipped classifier algebraRead ∧
                      Cont name route bridgeRead)
                  (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                  hsame ∧
                UnaryHistory algebraRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier flippedClassifierAlgebra nameRouteBridge algebraPkg bridgePkg
  have carrierProof :
      RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow
        transportRow route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, classifierUnary, flippedUnary,
    _sealUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _sourceWindowDyadic, _dyadicClassifierFlipped, _flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, _provenancePkg, _namePkg⟩ := carrier
  have algebraUnary : UnaryHistory algebraRead :=
    unary_cont_closed flippedUnary classifierUnary flippedClassifierAlgebra
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed nameUnary routeUnary nameRouteBridge
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeRead (And.intro (hsame_refl bridgeRead) carrierProof)
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
          intro _row _row' sameRows sourceRow
          exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            sourceRow.right
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, flippedClassifierAlgebra, nameRouteBridge⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, bridgePkg⟩
    }
  · exact ⟨algebraUnary, bridgeUnary⟩

theorem RegularCauchyNegationCarrier_limit_classifier_compatibility [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      limitRead realBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont classifier flipped limitRead ->
        Cont limitRead sealRow realBoundary ->
          PkgSig bundle limitRead pkg ->
            PkgSig bundle realBoundary pkg ->
              UnaryHistory classifier ∧ UnaryHistory flipped ∧ UnaryHistory limitRead ∧
                UnaryHistory sealRow ∧ UnaryHistory realBoundary ∧
                  Cont dyadic classifier flipped ∧ Cont classifier flipped limitRead ∧
                    Cont limitRead sealRow realBoundary ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle limitRead pkg ∧ PkgSig bundle realBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier classifierFlippedLimit limitSealBoundary limitPkg boundaryPkg
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, classifierUnary, flippedUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _sourceWindowDyadic,
    dyadicClassifierFlipped, _flippedSealTransport, _transportRouteProvenance,
    _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed classifierUnary flippedUnary classifierFlippedLimit
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed limitUnary sealUnary limitSealBoundary
  exact
    ⟨classifierUnary, flippedUnary, limitUnary, sealUnary, boundaryUnary,
      dyadicClassifierFlipped, classifierFlippedLimit, limitSealBoundary, provenancePkg,
      limitPkg, boundaryPkg⟩

theorem RegularCauchyNegationCarrier_apartness_nonescape [AskSetup] [PackageSetup]
    {source window dyadic classifier flipped sealRow transportRow route provenance name
      apartnessRead apartnessSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNegationCarrier source window dyadic classifier flipped sealRow transportRow
        route provenance name bundle pkg ->
      Cont flipped classifier apartnessRead ->
        Cont apartnessRead sealRow apartnessSeal ->
          PkgSig bundle apartnessSeal pkg ->
            UnaryHistory flipped ∧ UnaryHistory classifier ∧ UnaryHistory sealRow ∧
              UnaryHistory apartnessRead ∧ UnaryHistory apartnessSeal ∧
                Cont dyadic classifier flipped ∧ Cont flipped sealRow transportRow ∧
                  Cont flipped classifier apartnessRead ∧
                    Cont apartnessRead sealRow apartnessSeal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle apartnessSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier flippedClassifierApartness apartnessSealRoute apartnessSealPkg
  obtain ⟨_sourceUnary, _windowUnary, _dyadicUnary, classifierUnary, flippedUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _sourceWindowDyadic, dyadicClassifierFlipped, flippedSealTransport,
    _transportRouteProvenance, _sealProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have apartnessReadUnary : UnaryHistory apartnessRead :=
    unary_cont_closed flippedUnary classifierUnary flippedClassifierApartness
  have apartnessSealUnary : UnaryHistory apartnessSeal :=
    unary_cont_closed apartnessReadUnary sealUnary apartnessSealRoute
  exact
    ⟨flippedUnary, classifierUnary, sealUnary, apartnessReadUnary, apartnessSealUnary,
      dyadicClassifierFlipped, flippedSealTransport, flippedClassifierApartness,
      apartnessSealRoute, provenancePkg, apartnessSealPkg⟩

end BEDC.Derived.RegularCauchyNegationUp
