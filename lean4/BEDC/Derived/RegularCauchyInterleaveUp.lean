import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterleaveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyInterleavePacket [AskSetup] [PackageSetup]
    (left right merge windows modulus observations handoff transports routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory merge ∧ UnaryHistory windows ∧
    UnaryHistory modulus ∧ UnaryHistory observations ∧ UnaryHistory handoff ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont merge windows observations ∧
          Cont modulus observations handoff ∧ Cont routes provenance nameCert ∧
            PkgSig bundle handoff pkg

theorem RegularCauchyInterleavePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {left right merge windows modulus observations handoff transports routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavePacket left right merge windows modulus observations handoff
        transports routes provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
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

def RegularCauchyInterleaveCarrier [AskSetup] [PackageSetup]
    (I J S T W D M H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont I S T ∧ Cont T W D ∧ Cont D M endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyInterleaveWindowMergeExactness [AskSetup] [PackageSetup]
    {I J S T W D M H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleaveCarrier I J S T W D M H C P N endpoint bundle pkg ->
      UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
        UnaryHistory W ∧ UnaryHistory D ∧ Cont I S T ∧ Cont T W D ∧
          Cont D M endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, _mUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _endpointUnary, sourceWindow, windowDyadic,
    dyadicHandoff, pkgSig⟩ := carrier
  exact
    ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, sourceWindow, windowDyadic,
      dyadicHandoff, pkgSig⟩

theorem RegularCauchyInterleaveCarrier_selected_slot_exhaustion [AskSetup] [PackageSetup]
    {I J S T W D M H C P N endpoint selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleaveCarrier I J S T W D M H C P N endpoint bundle pkg ->
      Cont endpoint N selectedRead ->
        UnaryHistory selectedRead ∧ Cont I S T ∧ Cont T W D ∧ Cont D M endpoint ∧
          Cont endpoint N selectedRead ∧ PkgSig bundle endpoint pkg := by
  intro carrier selectedSlot
  obtain ⟨_iUnary, _jUnary, _sUnary, _tUnary, _wUnary, _dUnary, _mUnary, _hUnary,
    _cUnary, _pUnary, nUnary, endpointUnary, sourceWindow, windowDyadic,
    dyadicEndpoint, pkgSig⟩ := carrier
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed endpointUnary nUnary selectedSlot
  exact
    ⟨selectedReadUnary, sourceWindow, windowDyadic, dyadicEndpoint, selectedSlot, pkgSig⟩

theorem RegularCauchyInterleaveCarrier_classifier_transport_exactness [AskSetup] [PackageSetup]
    {I J S T W D M H C P N endpoint I' J' S' W' M' H' C' P' N' T' D'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleaveCarrier I J S T W D M H C P N endpoint bundle pkg ->
      hsame I I' ->
        hsame J J' ->
          hsame S S' ->
            hsame W W' ->
              hsame M M' ->
                hsame H H' ->
                  hsame C C' ->
                    hsame P P' ->
                      hsame N N' ->
                        Cont I' S' T' ->
                          Cont T' W' D' ->
                            Cont D' M' endpoint' ->
                              PkgSig bundle endpoint' pkg ->
                                RegularCauchyInterleaveCarrier I' J' S' T' W' D' M' H'
                                    C' P' N' endpoint' bundle pkg ∧
                                  hsame T T' ∧ hsame D D' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameI sameJ sameS sameW sameM sameH sameC sameP sameN sourceWindow'
    windowDyadic' dyadicEndpoint' endpointPkg'
  obtain ⟨iUnary, jUnary, sUnary, _tUnary, wUnary, _dUnary, mUnary, hUnary,
    cUnary, pUnary, nUnary, _endpointUnary, sourceWindow, windowDyadic,
    dyadicEndpoint, _pkgSig⟩ := carrier
  have iUnary' : UnaryHistory I' :=
    unary_transport iUnary sameI
  have jUnary' : UnaryHistory J' :=
    unary_transport jUnary sameJ
  have sUnary' : UnaryHistory S' :=
    unary_transport sUnary sameS
  have wUnary' : UnaryHistory W' :=
    unary_transport wUnary sameW
  have mUnary' : UnaryHistory M' :=
    unary_transport mUnary sameM
  have hUnary' : UnaryHistory H' :=
    unary_transport hUnary sameH
  have cUnary' : UnaryHistory C' :=
    unary_transport cUnary sameC
  have pUnary' : UnaryHistory P' :=
    unary_transport pUnary sameP
  have nUnary' : UnaryHistory N' :=
    unary_transport nUnary sameN
  have tUnary' : UnaryHistory T' :=
    unary_cont_closed iUnary' sUnary' sourceWindow'
  have dUnary' : UnaryHistory D' :=
    unary_cont_closed tUnary' wUnary' windowDyadic'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed dUnary' mUnary' dyadicEndpoint'
  have sameT : hsame T T' :=
    cont_respects_hsame sameI sameS sourceWindow sourceWindow'
  have sameD : hsame D D' :=
    cont_respects_hsame sameT sameW windowDyadic windowDyadic'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameD sameM dyadicEndpoint dyadicEndpoint'
  have transported :
      RegularCauchyInterleaveCarrier I' J' S' T' W' D' M' H' C' P' N' endpoint'
        bundle pkg :=
    ⟨iUnary', jUnary', sUnary', tUnary', wUnary', dUnary', mUnary', hUnary', cUnary',
      pUnary', nUnary', endpointUnary', sourceWindow', windowDyadic', dyadicEndpoint',
      endpointPkg'⟩
  exact ⟨transported, sameT, sameD, sameEndpoint⟩

end BEDC.Derived.RegularCauchyInterleaveUp
