import BEDC.Derived.ApophaticFixedPointFiberUp.TasteGate

namespace BEDC.Derived.ApophaticFixedPointFiberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticFixedPointFiber_public_export_surface
    (x : ApophaticFixedPointFiberUp) :
    ∃ digestSocket supplySocket gapFiber farEndBoundary inscription transport continuation
        provenance nameCert : BHist,
      apophaticFixedPointFiberFields x =
          [digestSocket, supplySocket, gapFiber, farEndBoundary, inscription, transport,
            continuation, provenance, nameCert] ∧
        apophaticFixedPointFiberToEventFlow x =
          [[BMark.b0], apophaticFixedPointFiberEncodeBHist digestSocket,
            [BMark.b1, BMark.b0], apophaticFixedPointFiberEncodeBHist supplySocket,
            [BMark.b1, BMark.b1, BMark.b0], apophaticFixedPointFiberEncodeBHist gapFiber,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              apophaticFixedPointFiberEncodeBHist farEndBoundary,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              apophaticFixedPointFiberEncodeBHist inscription,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              apophaticFixedPointFiberEncodeBHist transport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0], apophaticFixedPointFiberEncodeBHist continuation,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0], apophaticFixedPointFiberEncodeBHist provenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
              apophaticFixedPointFiberEncodeBHist nameCert] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk digestSocket supplySocket gapFiber farEndBoundary inscription transport continuation
      provenance nameCert =>
      exact
        ⟨digestSocket, supplySocket, gapFiber, farEndBoundary, inscription, transport,
          continuation, provenance, nameCert, rfl, rfl⟩

theorem ApophaticFixedPointFiber_scoped_route [AskSetup] [PackageSetup]
    {digest socket gap boundary inscription transport routes provenance name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg →
      UnaryHistory boundary →
        Cont inscription transport scopedRead →
          PkgSig bundle scopedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                    hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                      hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription
                      transport routes provenance name bundle pkg ∧
                      Cont digest socket gap ∧ Cont gap boundary inscription ∧
                        Cont inscription transport scopedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle scopedRead pkg)
                hsame ∧
              UnaryHistory gap ∧ UnaryHistory inscription ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryUnary scopedRoute scopedPkg
  have carrierWitness :
      ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg := carrier
  obtain ⟨digestUnary, socketUnary, transportUnary, _provenanceUnary, digestSocketGap,
    gapBoundaryInscription, _inscriptionTransportRoutes, provenancePkg, namePkg⟩ := carrier
  have gapUnary : UnaryHistory gap :=
    unary_cont_closed digestUnary socketUnary digestSocketGap
  have inscriptionUnary : UnaryHistory inscription :=
    unary_cont_closed gapUnary boundaryUnary gapBoundaryInscription
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed inscriptionUnary transportUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row digest ∨ hsame row socket ∨ hsame row gap ∨ hsame row boundary ∨
              hsame row inscription ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              ApophaticFixedPointFiberCarrier digest socket gap boundary inscription
                transport routes provenance name bundle pkg ∧
                Cont digest socket gap ∧ Cont gap boundary inscription ∧
                  Cont inscription transport scopedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierWitness, digestSocketGap, gapBoundaryInscription, scopedRoute,
          provenancePkg, namePkg, scopedPkg⟩
  }
  exact ⟨cert, gapUnary, inscriptionUnary, scopedUnary⟩

theorem ApophaticFixedPointFiber_bridge_readback [AskSetup] [PackageSetup]
    {digest socket gap boundary inscription transport routes provenance name bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg →
      UnaryHistory boundary →
        Cont inscription transport bridgeRead →
          PkgSig bundle digest pkg →
            PkgSig bundle socket pkg →
              PkgSig bundle gap pkg →
                PkgSig bundle boundary pkg →
                  PkgSig bundle inscription pkg →
                    PkgSig bundle bridgeRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                              hsame row boundary ∨ hsame row inscription ∨
                                hsame row transport ∨ hsame row routes ∨
                                  hsame row provenance ∨ hsame row name ∨
                                    hsame row bridgeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle digest pkg ∧
                              PkgSig bundle socket pkg ∧ PkgSig bundle gap pkg ∧
                                PkgSig bundle boundary pkg ∧
                                  PkgSig bundle inscription pkg ∧
                                    PkgSig bundle bridgeRead pkg ∧
                                      Cont digest socket gap ∧
                                        Cont gap boundary inscription ∧
                                          Cont inscription transport bridgeRead)
                          hsame ∧
                        PkgSig bundle bridgeRead pkg ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryUnary bridgeRoute digestPkg socketPkg gapPkg boundaryPkg inscriptionPkg
    bridgePkg
  obtain ⟨digestUnary, socketUnary, transportUnary, _provenanceUnary, digestSocketGap,
    gapBoundaryInscription, _inscriptionTransportRoutes, _provenancePkg, _namePkg⟩ := carrier
  have gapUnary : UnaryHistory gap :=
    unary_cont_closed digestUnary socketUnary digestSocketGap
  have inscriptionUnary : UnaryHistory inscription :=
    unary_cont_closed gapUnary boundaryUnary gapBoundaryInscription
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed inscriptionUnary transportUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row digest ∨ hsame row socket ∨ hsame row gap ∨ hsame row boundary ∨
              hsame row inscription ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle digest pkg ∧ PkgSig bundle socket pkg ∧
              PkgSig bundle gap pkg ∧ PkgSig bundle boundary pkg ∧
                PkgSig bundle inscription pkg ∧ PkgSig bundle bridgeRead pkg ∧
                  Cont digest socket gap ∧ Cont gap boundary inscription ∧
                    Cont inscription transport bridgeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, digestPkg, socketPkg, gapPkg, boundaryPkg, inscriptionPkg,
          bridgePkg, digestSocketGap, gapBoundaryInscription, bridgeRoute⟩
  }
  exact ⟨cert, bridgePkg, bridgeUnary⟩

theorem ApophaticFixedPointFiber_scoped_bridge_public_surface [AskSetup] [PackageSetup]
    {digest socket gap boundary inscription transport routes provenance name scopedRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg →
      UnaryHistory boundary →
        Cont inscription transport scopedRead →
          PkgSig bundle scopedRead pkg →
            Cont inscription transport bridgeRead →
              PkgSig bundle digest pkg →
                PkgSig bundle socket pkg →
                  PkgSig bundle gap pkg →
                    PkgSig bundle boundary pkg →
                      PkgSig bundle inscription pkg →
                        PkgSig bundle bridgeRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                                  hsame row boundary ∨ hsame row inscription ∨
                                    hsame row transport ∨ hsame row routes ∨
                                      hsame row provenance ∨ hsame row name ∨
                                        hsame row scopedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  ApophaticFixedPointFiberCarrier digest socket gap boundary
                                    inscription transport routes provenance name bundle pkg ∧
                                    Cont digest socket gap ∧
                                      Cont gap boundary inscription ∧
                                        Cont inscription transport scopedRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle name pkg ∧
                                              PkgSig bundle scopedRead pkg)
                              hsame ∧
                            SemanticNameCert
                                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                                    hsame row boundary ∨ hsame row inscription ∨
                                      hsame row transport ∨ hsame row routes ∨
                                        hsame row provenance ∨ hsame row name ∨
                                          hsame row bridgeRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle digest pkg ∧
                                    PkgSig bundle socket pkg ∧ PkgSig bundle gap pkg ∧
                                      PkgSig bundle boundary pkg ∧
                                        PkgSig bundle inscription pkg ∧
                                          PkgSig bundle bridgeRead pkg ∧
                                            Cont digest socket gap ∧
                                              Cont gap boundary inscription ∧
                                                Cont inscription transport bridgeRead)
                                hsame ∧
                              UnaryHistory scopedRead ∧ UnaryHistory bridgeRead ∧
                                PkgSig bundle scopedRead pkg ∧ PkgSig bundle bridgeRead pkg :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  by
    intro carrier boundaryUnary scopedRoute scopedPkg bridgeRoute digestPkg socketPkg gapPkg
      boundaryPkg inscriptionPkg bridgePkg
    have scopedSurface :=
      ApophaticFixedPointFiber_scoped_route (digest := digest) (socket := socket)
        (gap := gap) (boundary := boundary) (inscription := inscription)
        (transport := transport) (routes := routes) (provenance := provenance)
        (name := name) (scopedRead := scopedRead) (bundle := bundle) (pkg := pkg)
        carrier boundaryUnary scopedRoute scopedPkg
    have bridgeSurface :=
      ApophaticFixedPointFiber_bridge_readback (digest := digest) (socket := socket)
        (gap := gap) (boundary := boundary) (inscription := inscription)
        (transport := transport) (routes := routes) (provenance := provenance)
        (name := name) (bridgeRead := bridgeRead) (bundle := bundle) (pkg := pkg)
        carrier boundaryUnary bridgeRoute digestPkg socketPkg gapPkg boundaryPkg
        inscriptionPkg bridgePkg
    exact
      ⟨scopedSurface.left,
        bridgeSurface.left,
        scopedSurface.right.right.right,
        bridgeSurface.right.right,
        scopedPkg,
        bridgeSurface.right.left⟩

theorem ApophaticFixedPointFiber_mature_boundary [AskSetup] [PackageSetup]
    {digest socket gap boundary inscription transport routes provenance name publicRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticFixedPointFiberCarrier digest socket gap boundary inscription transport routes
        provenance name bundle pkg →
      UnaryHistory boundary →
        Cont inscription transport publicRead →
          PkgSig bundle publicRead pkg →
            Cont inscription transport bridgeRead →
              PkgSig bundle digest pkg →
                PkgSig bundle socket pkg →
                  PkgSig bundle gap pkg →
                    PkgSig bundle boundary pkg →
                      PkgSig bundle inscription pkg →
                        PkgSig bundle bridgeRead pkg →
                          hsame publicRead bridgeRead →
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                                    hsame row boundary ∨ hsame row inscription ∨
                                      hsame row transport ∨ hsame row routes ∨
                                        hsame row provenance ∨ hsame row name ∨
                                          hsame row publicRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    ApophaticFixedPointFiberCarrier digest socket gap boundary
                                      inscription transport routes provenance name bundle pkg ∧
                                      Cont digest socket gap ∧
                                        Cont gap boundary inscription ∧
                                          Cont inscription transport publicRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle name pkg ∧
                                                PkgSig bundle publicRead pkg)
                                hsame ∧
                              SemanticNameCert
                                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row digest ∨ hsame row socket ∨ hsame row gap ∨
                                      hsame row boundary ∨ hsame row inscription ∨
                                        hsame row transport ∨ hsame row routes ∨
                                          hsame row provenance ∨ hsame row name ∨
                                            hsame row bridgeRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle digest pkg ∧
                                      PkgSig bundle socket pkg ∧ PkgSig bundle gap pkg ∧
                                        PkgSig bundle boundary pkg ∧
                                          PkgSig bundle inscription pkg ∧
                                            PkgSig bundle bridgeRead pkg ∧
                                              Cont digest socket gap ∧
                                                Cont gap boundary inscription ∧
                                                  Cont inscription transport bridgeRead)
                                  hsame ∧
                                hsame publicRead bridgeRead ∧ UnaryHistory publicRead ∧
                                  UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier boundaryUnary publicRoute publicPkg bridgeRoute digestPkg socketPkg gapPkg
    boundaryPkg inscriptionPkg bridgePkg publicBridge
  have surface :=
    ApophaticFixedPointFiber_scoped_bridge_public_surface (digest := digest)
      (socket := socket) (gap := gap) (boundary := boundary)
      (inscription := inscription) (transport := transport) (routes := routes)
      (provenance := provenance) (name := name) (scopedRead := publicRead)
      (bridgeRead := bridgeRead) (bundle := bundle) (pkg := pkg) carrier boundaryUnary
      publicRoute publicPkg bridgeRoute digestPkg socketPkg gapPkg boundaryPkg inscriptionPkg
      bridgePkg
  exact
    ⟨surface.left, surface.right.left, publicBridge, surface.right.right.left,
      surface.right.right.right.left⟩

end BEDC.Derived.ApophaticFixedPointFiberUp
