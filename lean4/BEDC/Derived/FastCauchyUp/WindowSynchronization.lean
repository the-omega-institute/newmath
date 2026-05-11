import BEDC.Derived.FastCauchyUp

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchyFinitePacket_modulus_synchronization_common_regseqrat_window
    [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      stream' endpoint' radius' latePair' transportWindow' regWindow' sealBoundary' certRow'
      precision selectedThreshold selectedEndpoint selectedLatePair selectedWindow selectedRead
      selectedEndpoint' selectedLatePair' selectedWindow' selectedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      FastCauchyFinitePacket stream' modulus endpoint' radius' latePair' transportWindow'
          regWindow' sealBoundary' certRow' bundle pkg ->
        UnaryHistory precision ->
          hsame endpoint endpoint' ->
            hsame latePair latePair' ->
              Cont modulus precision selectedThreshold ->
                Cont endpoint precision selectedEndpoint ->
                  Cont latePair precision selectedLatePair ->
                    Cont selectedThreshold selectedEndpoint selectedWindow ->
                      Cont selectedLatePair selectedWindow selectedRead ->
                        Cont endpoint' precision selectedEndpoint' ->
                          Cont latePair' precision selectedLatePair' ->
                            Cont selectedThreshold selectedEndpoint' selectedWindow' ->
                              Cont selectedLatePair' selectedWindow' selectedRead' ->
                                PkgSig bundle selectedRead pkg ->
                                  PkgSig bundle selectedRead' pkg ->
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        FastCauchyFinitePacket stream modulus endpoint radius
                                            latePair transportWindow regWindow sealBoundary
                                            certRow bundle pkg ∧
                                          FastCauchyFinitePacket stream' modulus endpoint'
                                            radius' latePair' transportWindow' regWindow'
                                            sealBoundary' certRow' bundle pkg ∧
                                          UnaryHistory precision ∧
                                          hsame endpoint endpoint' ∧ hsame latePair latePair' ∧
                                          Cont modulus precision selectedThreshold ∧
                                          Cont endpoint precision selectedEndpoint ∧
                                          Cont latePair precision selectedLatePair ∧
                                          Cont selectedThreshold selectedEndpoint selectedWindow ∧
                                          Cont selectedLatePair selectedWindow selectedRead ∧
                                          Cont endpoint' precision selectedEndpoint' ∧
                                          Cont latePair' precision selectedLatePair' ∧
                                          Cont selectedThreshold selectedEndpoint'
                                            selectedWindow' ∧
                                          Cont selectedLatePair' selectedWindow' selectedRead' ∧
                                          PkgSig bundle selectedRead pkg ∧
                                          PkgSig bundle selectedRead' pkg ∧
                                          hsame selectedEndpoint selectedEndpoint' ∧
                                          hsame selectedLatePair selectedLatePair' ∧
                                          hsame selectedWindow selectedWindow' ∧
                                          hsame selectedRead selectedRead' ∧
                                          (hsame row selectedRead ∨ hsame row selectedRead'))
                                      (fun row : BHist =>
                                        FastCauchyFinitePacket stream modulus endpoint radius
                                            latePair transportWindow regWindow sealBoundary
                                            certRow bundle pkg ∧
                                          FastCauchyFinitePacket stream' modulus endpoint'
                                            radius' latePair' transportWindow' regWindow'
                                            sealBoundary' certRow' bundle pkg ∧
                                          UnaryHistory precision ∧
                                          hsame endpoint endpoint' ∧ hsame latePair latePair' ∧
                                          Cont modulus precision selectedThreshold ∧
                                          Cont endpoint precision selectedEndpoint ∧
                                          Cont latePair precision selectedLatePair ∧
                                          Cont selectedThreshold selectedEndpoint selectedWindow ∧
                                          Cont selectedLatePair selectedWindow selectedRead ∧
                                          Cont endpoint' precision selectedEndpoint' ∧
                                          Cont latePair' precision selectedLatePair' ∧
                                          Cont selectedThreshold selectedEndpoint'
                                            selectedWindow' ∧
                                          Cont selectedLatePair' selectedWindow' selectedRead' ∧
                                          PkgSig bundle selectedRead pkg ∧
                                          PkgSig bundle selectedRead' pkg ∧
                                          hsame selectedEndpoint selectedEndpoint' ∧
                                          hsame selectedLatePair selectedLatePair' ∧
                                          hsame selectedWindow selectedWindow' ∧
                                          hsame selectedRead selectedRead' ∧
                                          (hsame row selectedRead ∨ hsame row selectedRead'))
                                      (fun row : BHist =>
                                        FastCauchyFinitePacket stream modulus endpoint radius
                                            latePair transportWindow regWindow sealBoundary
                                            certRow bundle pkg ∧
                                          FastCauchyFinitePacket stream' modulus endpoint'
                                            radius' latePair' transportWindow' regWindow'
                                            sealBoundary' certRow' bundle pkg ∧
                                          UnaryHistory precision ∧
                                          hsame endpoint endpoint' ∧ hsame latePair latePair' ∧
                                          Cont modulus precision selectedThreshold ∧
                                          Cont endpoint precision selectedEndpoint ∧
                                          Cont latePair precision selectedLatePair ∧
                                          Cont selectedThreshold selectedEndpoint selectedWindow ∧
                                          Cont selectedLatePair selectedWindow selectedRead ∧
                                          Cont endpoint' precision selectedEndpoint' ∧
                                          Cont latePair' precision selectedLatePair' ∧
                                          Cont selectedThreshold selectedEndpoint'
                                            selectedWindow' ∧
                                          Cont selectedLatePair' selectedWindow' selectedRead' ∧
                                          PkgSig bundle selectedRead pkg ∧
                                          PkgSig bundle selectedRead' pkg ∧
                                          hsame selectedEndpoint selectedEndpoint' ∧
                                          hsame selectedLatePair selectedLatePair' ∧
                                          hsame selectedWindow selectedWindow' ∧
                                          hsame selectedRead selectedRead' ∧
                                          (hsame row selectedRead ∨ hsame row selectedRead'))
                                      hsame := by
  intro packet packet' precisionUnary sameEndpoint sameLatePair thresholdRow endpointRow
    latePairRow windowRow readRow endpointRow' latePairRow' windowRow' readRow' pkgRow pkgRow'
  have cofinality :=
    FastCauchyFinitePacket_dyadicprecision_window_cofinality packet precisionUnary thresholdRow
      endpointRow latePairRow windowRow readRow pkgRow
  have cofinality' :=
    FastCauchyFinitePacket_dyadicprecision_window_cofinality packet' precisionUnary thresholdRow
      endpointRow' latePairRow' windowRow' readRow' pkgRow'
  have selectedEndpointSame : hsame selectedEndpoint selectedEndpoint' :=
    cont_respects_hsame sameEndpoint (hsame_refl precision)
      cofinality.right.right.right.right.right.right.left
      cofinality'.right.right.right.right.right.right.left
  have selectedLatePairSame : hsame selectedLatePair selectedLatePair' :=
    cont_respects_hsame sameLatePair (hsame_refl precision)
      cofinality.right.right.right.right.right.right.right.left
      cofinality'.right.right.right.right.right.right.right.left
  have selectedWindowSame : hsame selectedWindow selectedWindow' :=
    cont_respects_hsame (hsame_refl selectedThreshold) selectedEndpointSame
      cofinality.right.right.right.right.right.right.right.right.left
      cofinality'.right.right.right.right.right.right.right.right.left
  have selectedReadSame : hsame selectedRead selectedRead' :=
    cont_respects_hsame selectedLatePairSame selectedWindowSame
      cofinality.right.right.right.right.right.right.right.right.right.left
      cofinality'.right.right.right.right.right.right.right.right.right.left
  let Source := fun row : BHist =>
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ∧
      FastCauchyFinitePacket stream' modulus endpoint' radius' latePair' transportWindow'
        regWindow' sealBoundary' certRow' bundle pkg ∧
      UnaryHistory precision ∧ hsame endpoint endpoint' ∧ hsame latePair latePair' ∧
      Cont modulus precision selectedThreshold ∧ Cont endpoint precision selectedEndpoint ∧
      Cont latePair precision selectedLatePair ∧
      Cont selectedThreshold selectedEndpoint selectedWindow ∧
      Cont selectedLatePair selectedWindow selectedRead ∧
      Cont endpoint' precision selectedEndpoint' ∧
      Cont latePair' precision selectedLatePair' ∧
      Cont selectedThreshold selectedEndpoint' selectedWindow' ∧
      Cont selectedLatePair' selectedWindow' selectedRead' ∧
      PkgSig bundle selectedRead pkg ∧ PkgSig bundle selectedRead' pkg ∧
      hsame selectedEndpoint selectedEndpoint' ∧ hsame selectedLatePair selectedLatePair' ∧
      hsame selectedWindow selectedWindow' ∧ hsame selectedRead selectedRead' ∧
      (hsame row selectedRead ∨ hsame row selectedRead')
  have sourceAtRead : Source selectedRead :=
    ⟨packet, packet', precisionUnary, sameEndpoint, sameLatePair, thresholdRow, endpointRow,
      latePairRow, windowRow, readRow, endpointRow', latePairRow', windowRow', readRow',
      pkgRow, pkgRow', selectedEndpointSame, selectedLatePairSame, selectedWindowSame,
      selectedReadSame, Or.inl (hsame_refl selectedRead)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro selectedRead sourceAtRead
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
          source.right.right.right.left, source.right.right.right.right.left,
          source.right.right.right.right.right.left,
          source.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
          ?_⟩
        cases source.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right with
        | inl sameRead =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRead)
        | inr sameRead' =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameRead')
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.FastCauchyUp
