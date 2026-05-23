import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenPhaseRootUnblockConsumerReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead endpointRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window phaseRead ->
        Cont phaseRead radius endpointRead ->
          Cont endpointRead nameRow consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory phaseRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory consumerRead ∧ Cont cover window phaseRead ∧
                  Cont phaseRead radius endpointRead ∧ Cont endpointRead nameRow consumerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverWindowPhase phaseRadiusEndpoint endpointNameConsumer consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed coverUnary windowUnary coverWindowPhase
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed phaseUnary radiusUnary phaseRadiusEndpoint
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary nameRowUnary endpointNameConsumer
  exact
    ⟨phaseUnary, endpointUnary, consumerUnary, coverWindowPhase, phaseRadiusEndpoint,
      endpointNameConsumer, provenancePkg, consumerPkg⟩

theorem FiniteLebesgueNumberRootUnblockEndpointUniformity [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead endpointLeft
      endpointRight consumerLeft consumerRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius endpointLeft ->
          Cont rootRead radius endpointRight ->
            Cont endpointLeft nameRow consumerLeft ->
              Cont endpointRight nameRow consumerRight ->
                PkgSig bundle consumerLeft pkg ->
                  PkgSig bundle consumerRight pkg ->
                    hsame endpointLeft endpointRight ∧ hsame consumerLeft consumerRight ∧
                      UnaryHistory endpointLeft ∧ UnaryHistory endpointRight ∧
                        UnaryHistory consumerLeft ∧ UnaryHistory consumerRight := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusLeft rootRadiusRight leftConsumer rightConsumer
    _leftPkg _rightPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have sameEndpoint : hsame endpointLeft endpointRight :=
    cont_deterministic rootRadiusLeft rootRadiusRight
  have endpointLeftUnary : UnaryHistory endpointLeft :=
    unary_cont_closed rootUnary radiusUnary rootRadiusLeft
  have endpointRightUnary : UnaryHistory endpointRight :=
    unary_transport endpointLeftUnary sameEndpoint
  have consumerLeftUnary : UnaryHistory consumerLeft :=
    unary_cont_closed endpointLeftUnary nameRowUnary leftConsumer
  have consumerRightUnary : UnaryHistory consumerRight :=
    unary_cont_closed endpointRightUnary nameRowUnary rightConsumer
  have sameConsumer : hsame consumerLeft consumerRight :=
    cont_respects_hsame sameEndpoint (hsame_refl nameRow) leftConsumer rightConsumer
  exact
    ⟨sameEndpoint, sameConsumer, endpointLeftUnary, endpointRightUnary, consumerLeftUnary,
      consumerRightUnary⟩

theorem FiniteLebesgueNumberRootRadiusExportExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row rootRead ∨ hsame row phaseRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                      hsame row consumerRead)
                  hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory phaseRead ∧ UnaryHistory consumerRead ∧
                  Cont route nameRow rootRead ∧ Cont rootRead radius phaseRead ∧
                    Cont phaseRead mesh consumerRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameRoot rootRadiusPhase phaseMeshConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row rootRead ∨ hsame row phaseRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, consumerPkg, source.left⟩
    }
  exact
    ⟨cert, rootUnary, phaseUnary, consumerUnary, routeNameRoot, rootRadiusPhase,
      phaseMeshConsumer, provenancePkg, consumerPkg⟩

theorem FiniteLebesgueNumberFourFaceRadiusExitDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead endpointLeft
      endpointRight consumerLeft consumerRight exitLeft exitRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius endpointLeft ->
          Cont rootRead radius endpointRight ->
            Cont endpointLeft mesh consumerLeft ->
              Cont endpointRight mesh consumerRight ->
                Cont consumerLeft nameRow exitLeft ->
                  Cont consumerRight nameRow exitRight ->
                    PkgSig bundle exitLeft pkg ->
                      PkgSig bundle exitRight pkg ->
                        hsame endpointLeft endpointRight ∧
                          hsame consumerLeft consumerRight ∧ hsame exitLeft exitRight ∧
                            UnaryHistory endpointLeft ∧ UnaryHistory endpointRight ∧
                              UnaryHistory consumerLeft ∧ UnaryHistory consumerRight ∧
                                UnaryHistory exitLeft ∧ UnaryHistory exitRight := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusLeft rootRadiusRight leftConsumer rightConsumer
    leftExit rightExit _leftPkg _rightPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have sameEndpoint : hsame endpointLeft endpointRight :=
    cont_deterministic rootRadiusLeft rootRadiusRight
  have endpointLeftUnary : UnaryHistory endpointLeft :=
    unary_cont_closed rootUnary radiusUnary rootRadiusLeft
  have endpointRightUnary : UnaryHistory endpointRight :=
    unary_transport endpointLeftUnary sameEndpoint
  have consumerLeftUnary : UnaryHistory consumerLeft :=
    unary_cont_closed endpointLeftUnary meshUnary leftConsumer
  have consumerRightUnary : UnaryHistory consumerRight :=
    unary_cont_closed endpointRightUnary meshUnary rightConsumer
  have sameConsumer : hsame consumerLeft consumerRight :=
    cont_respects_hsame sameEndpoint (hsame_refl mesh) leftConsumer rightConsumer
  have exitLeftUnary : UnaryHistory exitLeft :=
    unary_cont_closed consumerLeftUnary nameRowUnary leftExit
  have exitRightUnary : UnaryHistory exitRight :=
    unary_cont_closed consumerRightUnary nameRowUnary rightExit
  have sameExit : hsame exitLeft exitRight :=
    cont_respects_hsame sameConsumer (hsame_refl nameRow) leftExit rightExit
  exact
    ⟨sameEndpoint, sameConsumer, sameExit, endpointLeftUnary, endpointRightUnary,
      consumerLeftUnary, consumerRightUnary, exitLeftUnary, exitRightUnary⟩

theorem FiniteLebesgueNumberOpenPhasePositiveRadiusStability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead radius'
      mesh' stabilizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          hsame radius radius' ->
            hsame mesh mesh' ->
              Cont radius' mesh' stabilizedRead ->
                UnaryHistory rootRead ∧ UnaryHistory phaseRead ∧
                  UnaryHistory stabilizedRead ∧ Cont rootRead radius phaseRead ∧
                    Cont radius' mesh' stabilizedRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusPhase sameRadius sameMesh stabilizedCont
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have radiusPrimeUnary : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have meshPrimeUnary : UnaryHistory mesh' :=
    unary_transport meshUnary sameMesh
  have stabilizedUnary : UnaryHistory stabilizedRead :=
    unary_cont_closed radiusPrimeUnary meshPrimeUnary stabilizedCont
  exact
    ⟨rootUnary, phaseUnary, stabilizedUnary, rootRadiusPhase, stabilizedCont,
      provenancePkg⟩

theorem FiniteLebesgueNumberFourFaceRadiusExitCoverage_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {cover radius mesh stream regular real transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance nameRow
        bundle pkg →
      Cont cover radius stream →
        Cont stream regular real →
          PkgSig bundle real pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row real ∧
                    FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance
                      nameRow bundle pkg)
                (fun row : BHist =>
                  hsame row real ∧ Cont cover radius stream ∧ Cont stream regular real)
                (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
                hsame ∧
              Cont cover radius stream ∧ Cont stream regular real ∧
                PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusStream streamRegularReal realPkg
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance
            nameRow bundle pkg) real := by
    exact ⟨hsame_refl real, carrier⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius stream ∧ Cont stream regular real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro real sourceReal
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, coverRadiusStream, streamRegularReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact ⟨cert, coverRadiusStream, streamRegularReal, realPkg⟩

theorem FiniteLebesgueNumberFourFaceRadiusExitNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead endpointRead realRead
      triadRead exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window phaseRead ->
        Cont phaseRead radius endpointRead ->
          Cont endpointRead route realRead ->
            Cont realRead nameRow triadRead ->
              Cont triadRead mesh exitRead ->
                PkgSig bundle exitRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row phaseRead ∨ hsame row endpointRead ∨
                          hsame row realRead ∨ hsame row triadRead ∨ hsame row exitRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle exitRead pkg ∧
                          hsame row exitRead)
                      hsame ∧
                    UnaryHistory phaseRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory realRead ∧ UnaryHistory triadRead ∧
                        UnaryHistory exitRead ∧ Cont cover window phaseRead ∧
                          Cont phaseRead radius endpointRead ∧
                            Cont endpointRead route realRead ∧ Cont realRead nameRow triadRead ∧
                              Cont triadRead mesh exitRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle exitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverWindowPhase phaseRadiusEndpoint endpointRouteReal realNameTriad
    triadMeshExit exitPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed coverUnary windowUnary coverWindowPhase
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed phaseUnary radiusUnary phaseRadiusEndpoint
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteReal
  have triadUnary : UnaryHistory triadRead :=
    unary_cont_closed realUnary nameRowUnary realNameTriad
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed triadUnary meshUnary triadMeshExit
  have sourceExit :
      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row) exitRead := by
    exact ⟨hsame_refl exitRead, exitUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row phaseRead ∨ hsame row endpointRead ∨
              hsame row realRead ∨ hsame row triadRead ∨ hsame row exitRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle exitRead pkg ∧
              hsame row exitRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exitRead sourceExit
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
        exact ⟨provenancePkg, exitPkg, source.left⟩
    }
  exact
    ⟨cert, phaseUnary, endpointUnary, realUnary, triadUnary, exitUnary, coverWindowPhase,
      phaseRadiusEndpoint, endpointRouteReal, realNameTriad, triadMeshExit, provenancePkg,
      exitPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
