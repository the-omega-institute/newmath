import BEDC.Derived.DyadicCoverUp

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoverPacket_ledger_nonescape [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint
      consumerRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg →
      Cont endpoint routes consumerRead →
        Cont consumerRead routes completionRead →
          PkgSig bundle consumerRead pkg →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row consumerRead ∨ hsame row completionRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row centers ∨ hsame row radii ∨ hsame row intervals ∨
                      hsame row window ∨ hsame row endpoint ∨ hsame row consumerRead ∨
                        hsame row completionRead)
                  (fun row : BHist =>
                    (hsame row consumerRead ∧ PkgSig bundle consumerRead pkg) ∨
                      (hsame row completionRead ∧ PkgSig bundle completionRead pkg))
                  hsame ∧
                UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
                  UnaryHistory window ∧ UnaryHistory endpoint ∧ UnaryHistory consumerRead ∧
                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet endpointRoutesConsumer consumerRoutesCompletion consumerPkg completionPkg
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, endpointUnary,
    _centersRadiiIntervals, _intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    _endpointPkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary routesUnary endpointRoutesConsumer
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed consumerUnary routesUnary consumerRoutesCompletion
  have sourceAtConsumer :
      (hsame consumerRead consumerRead ∨ hsame consumerRead completionRead) ∧
        UnaryHistory consumerRead :=
    ⟨Or.inl (hsame_refl consumerRead), consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row consumerRead ∨ hsame row completionRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row centers ∨ hsame row radii ∨ hsame row intervals ∨
              hsame row window ∨ hsame row endpoint ∨ hsame row consumerRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            (hsame row consumerRead ∧ PkgSig bundle consumerRead pkg) ∨
              (hsame row completionRead ∧ PkgSig bundle completionRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
        cases source.left with
        | inl sameConsumer =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameConsumer),
                unary_transport source.right sameRows⟩
        | inr sameCompletion =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameConsumer =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameConsumer)))))
      | inr sameCompletion =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameCompletion)))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameConsumer => exact Or.inl ⟨sameConsumer, consumerPkg⟩
      | inr sameCompletion => exact Or.inr ⟨sameCompletion, completionPkg⟩
  }
  exact
    ⟨cert, centersUnary, radiiUnary, intervalsUnary, windowUnary, endpointUnary,
      consumerUnary, completionUnary⟩

theorem DyadicCoverPacket_total_bounded_bridge [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint incidence
      radiusRead envelopeRead totalBoundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      Cont window routes incidence ->
        Cont radii incidence radiusRead ->
          Cont incidence routes envelopeRead ->
            Cont centers radii totalBoundedRead ->
              PkgSig bundle incidence pkg ->
                PkgSig bundle radiusRead pkg ->
                  PkgSig bundle envelopeRead pkg ->
                    PkgSig bundle totalBoundedRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row endpoint ∧
                              DyadicCoverPacket centers radii intervals mesh window transport routes
                                provenance nameCert endpoint bundle pkg)
                          (fun row : BHist => hsame row endpoint)
                          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                          hsame ∧
                        UnaryHistory centers ∧
                        UnaryHistory radii ∧
                        UnaryHistory intervals ∧
                        UnaryHistory window ∧
                        UnaryHistory incidence ∧
                        UnaryHistory radiusRead ∧
                        UnaryHistory envelopeRead ∧
                        UnaryHistory totalBoundedRead ∧
                        Cont centers radii intervals ∧
                        Cont intervals mesh window ∧
                        Cont window routes incidence ∧
                        Cont radii incidence radiusRead ∧
                        Cont incidence routes envelopeRead ∧
                        Cont centers radii totalBoundedRead ∧
                        PkgSig bundle endpoint pkg ∧
                        PkgSig bundle incidence pkg ∧
                        PkgSig bundle radiusRead pkg ∧
                        PkgSig bundle envelopeRead pkg ∧
                        PkgSig bundle totalBoundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet windowRoutesIncidence radiiIncidenceRadiusRead incidenceRoutesEnvelopeRead
    centersRadiiTotal incidencePkg radiusReadPkg envelopeReadPkg totalBoundedPkg
  have certSurface :=
    DyadicCoverPacket_namecert_obligations packet
  obtain ⟨centersUnary, radiiUnary, intervalsUnary, _meshUnary, windowUnary,
    _transportUnary, routesUnary, _provenanceUnary, _nameCertUnary, _endpointUnary,
    centersRadiiIntervals, intervalsMeshWindow, _windowRoutesEndpoint, _nameCertEndpoint,
    endpointPkg⟩ := packet
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed windowUnary routesUnary windowRoutesIncidence
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary incidenceUnary radiiIncidenceRadiusRead
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed incidenceUnary routesUnary incidenceRoutesEnvelopeRead
  have totalBoundedUnary : UnaryHistory totalBoundedRead :=
    unary_cont_closed centersUnary radiiUnary centersRadiiTotal
  exact
    ⟨certSurface.left,
      centersUnary,
      radiiUnary,
      intervalsUnary,
      windowUnary,
      incidenceUnary,
      radiusReadUnary,
      envelopeReadUnary,
      totalBoundedUnary,
      centersRadiiIntervals,
      intervalsMeshWindow,
      windowRoutesIncidence,
      radiiIncidenceRadiusRead,
      incidenceRoutesEnvelopeRead,
      centersRadiiTotal,
      endpointPkg,
      incidencePkg,
      radiusReadPkg,
      envelopeReadPkg,
      totalBoundedPkg⟩

end BEDC.Derived.DyadicCoverUp
