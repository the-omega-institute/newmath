import BEDC.Derived.FastCauchyUp

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

theorem FastCauchyFinitePacket_explicit_rate_seal_window_exhaustion [AskSetup]
    [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      precision selectedThreshold selectedEndpoint selectedLatePair selectedWindow selectedRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory precision ->
        Cont modulus precision selectedThreshold ->
          Cont endpoint precision selectedEndpoint ->
            Cont latePair precision selectedLatePair ->
              Cont selectedThreshold selectedEndpoint selectedWindow ->
                Cont selectedLatePair selectedWindow selectedRead ->
                  Cont selectedRead sealBoundary realSeal ->
                    PkgSig bundle realSeal pkg ->
                      UnaryHistory selectedThreshold ∧ UnaryHistory selectedEndpoint ∧
                        UnaryHistory selectedLatePair ∧ UnaryHistory selectedWindow ∧
                          UnaryHistory selectedRead ∧ UnaryHistory realSeal ∧
                            Cont selectedRead sealBoundary realSeal ∧
                              PkgSig bundle realSeal pkg := by
  intro packet precisionUnary thresholdRow endpointRow latePairRow windowRow readRow sealRow pkgRow
  obtain ⟨_streamUnary, modulusUnary, endpointUnary, _radiusUnary, latePairUnary,
    _transportUnary, _regUnary, sealUnary, _certUnary, _streamModulusRoute,
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
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readUnary sealUnary sealRow
  exact ⟨thresholdUnary, endpointSelectedUnary, latePairSelectedUnary, windowUnary,
    readUnary, realSealUnary, sealRow, pkgRow⟩

end BEDC.Derived.FastCauchyUp
