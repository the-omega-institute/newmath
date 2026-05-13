import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealDiagonalCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealDiagonalCompletionSourcePacket [AskSetup] [PackageSetup]
    (inputFamily modulus selector schedule readback «seal» provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory inputFamily ∧ UnaryHistory modulus ∧ UnaryHistory schedule ∧
    UnaryHistory «seal» ∧ UnaryHistory provenance ∧ Cont inputFamily modulus selector ∧
      Cont selector schedule readback ∧ Cont readback «seal» localCert ∧
        Cont localCert provenance «seal» ∧ PkgSig bundle provenance pkg

theorem RealDiagonalCompletionSourcePacket_carrier_habitation [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback «seal» provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory inputFamily ->
      UnaryHistory modulus ->
        UnaryHistory schedule ->
          UnaryHistory «seal» ->
            UnaryHistory provenance ->
              Cont inputFamily modulus selector ->
                Cont selector schedule readback ->
                  Cont readback «seal» localCert ->
                    Cont localCert provenance «seal» ->
                      PkgSig bundle provenance pkg ->
                        RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule
                            readback «seal» provenance localCert bundle pkg ∧
                          UnaryHistory selector ∧ UnaryHistory readback ∧
                            UnaryHistory localCert := by
  intro inputUnary modulusUnary scheduleUnary sealUnary provenanceUnary selectorRow
    readbackRow localCertRow sealRow provenanceSig
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary selectorRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary readbackRow
  have localCertUnary : UnaryHistory localCert :=
    unary_cont_closed readbackUnary sealUnary localCertRow
  exact
    ⟨⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, provenanceUnary, selectorRow,
        readbackRow, localCertRow, sealRow, provenanceSig⟩,
      selectorUnary, readbackUnary, localCertUnary⟩

theorem RealDiagonalCompletionSourcePacket_ledger_exactness [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback «seal» provenance localCert consumerRead
      diagonalRead rationalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback «seal»
        provenance localCert bundle pkg ->
      Cont selector schedule diagonalRead ->
        Cont diagonalRead readback rationalRead ->
          Cont rationalRead «seal» consumerRead ->
            UnaryHistory selector ∧ UnaryHistory schedule ∧ UnaryHistory readback ∧
              UnaryHistory «seal» ∧ UnaryHistory diagonalRead ∧ UnaryHistory rationalRead ∧
                UnaryHistory consumerRead ∧ Cont selector schedule diagonalRead ∧
                  Cont diagonalRead readback rationalRead ∧
                    Cont rationalRead «seal» consumerRead ∧ PkgSig bundle provenance pkg := by
  intro packet diagonalRow rationalRow consumerRow
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, _provenanceUnary,
    _selectorRow, _readbackRow, _localCertRow, _sealRow, pkgSig⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary _selectorRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary _readbackRow
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectorUnary scheduleUnary diagonalRow
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed diagonalUnary readbackUnary rationalRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rationalUnary sealUnary consumerRow
  exact
    ⟨selectorUnary, scheduleUnary, readbackUnary, sealUnary, diagonalUnary,
      rationalUnary, consumerUnary, diagonalRow, rationalRow, consumerRow, pkgSig⟩

theorem RealDiagonalCompletionSourcePacket_classifier_stability [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback sealRow provenance localCert selectorNew
      scheduleNew readbackNew sealNew localCertNew : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback sealRow
        provenance localCert bundle pkg ->
      hsame selector selectorNew ->
        hsame schedule scheduleNew ->
          hsame readback readbackNew ->
            hsame sealRow sealNew ->
              Cont inputFamily modulus selectorNew ->
                Cont selectorNew scheduleNew readbackNew ->
                  Cont readbackNew sealNew localCertNew ->
                    Cont localCertNew provenance sealNew ->
                      RealDiagonalCompletionSourcePacket inputFamily modulus selectorNew
                          scheduleNew readbackNew sealNew provenance localCertNew bundle pkg ∧
                        hsame localCert localCertNew := by
  intro packet sameSelector sameSchedule sameReadback sameSeal selectorRowNew readbackRowNew
    localCertRowNew sealRowNew
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, provenanceUnary, _selectorRow,
    _readbackRow, localCertRow, _sealRow, pkgSig⟩ := packet
  have scheduleUnaryNew : UnaryHistory scheduleNew :=
    unary_transport scheduleUnary sameSchedule
  have sealUnaryNew : UnaryHistory sealNew :=
    unary_transport sealUnary sameSeal
  have sameLocalCert : hsame localCert localCertNew :=
    cont_respects_hsame sameReadback sameSeal localCertRow localCertRowNew
  exact
    ⟨⟨inputUnary,
        modulusUnary,
        scheduleUnaryNew,
        sealUnaryNew,
        provenanceUnary,
        selectorRowNew,
        readbackRowNew,
        localCertRowNew,
        sealRowNew,
        pkgSig⟩,
      sameLocalCert⟩

theorem RealDiagonalCompletionSourcePacket_seal_factorization [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback sealRow provenance localCert diagonalRead
      diagonalRead' rationalRead rationalRead' consumerRead consumerRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback sealRow
        provenance localCert bundle pkg ->
      Cont selector schedule diagonalRead ->
        Cont selector schedule diagonalRead' ->
          Cont diagonalRead readback rationalRead ->
            Cont diagonalRead' readback rationalRead' ->
              Cont rationalRead sealRow consumerRead ->
                Cont rationalRead' sealRow consumerRead' ->
                  hsame diagonalRead diagonalRead' ->
                    hsame rationalRead rationalRead' ∧ hsame consumerRead consumerRead' ∧
                      UnaryHistory rationalRead ∧ UnaryHistory consumerRead ∧
                        PkgSig bundle provenance pkg := by
  intro packet diagonalRow diagonalRow' rationalRow rationalRow' consumerRow consumerRow'
    sameDiagonal
  have exactness :=
    RealDiagonalCompletionSourcePacket_ledger_exactness packet diagonalRow rationalRow consumerRow
  have sameRational : hsame rationalRead rationalRead' :=
    cont_respects_hsame sameDiagonal (hsame_refl readback) rationalRow rationalRow'
  have sameConsumer : hsame consumerRead consumerRead' :=
    cont_respects_hsame sameRational (hsame_refl sealRow) consumerRow consumerRow'
  exact
    ⟨sameRational, sameConsumer, exactness.right.right.right.right.right.left,
      exactness.right.right.right.right.right.right.left,
      exactness.right.right.right.right.right.right.right.right.right.right⟩

theorem RealDiagonalCompletionSourcePacket_window_extraction [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback sealRow provenance localCert precision
      selectedWindow selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback sealRow
        provenance localCert bundle pkg ->
      Cont modulus selector precision ->
        Cont precision schedule selectedWindow ->
          Cont selectedWindow readback selectedRead ->
            UnaryHistory precision ∧ UnaryHistory selectedWindow ∧
              UnaryHistory selectedRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet precisionRoute windowRoute readRoute
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, _sealUnary, _provenanceUnary, selectorRoute,
    readbackRoute, _localCertRoute, _sealRoute, provenancePkg⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary selectorRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary readbackRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed modulusUnary selectorUnary precisionRoute
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed precisionUnary scheduleUnary windowRoute
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectedWindowUnary readbackUnary readRoute
  exact ⟨precisionUnary, selectedWindowUnary, selectedReadUnary, provenancePkg⟩

theorem RealDiagonalCompletionSourcePacket_namecert_obligation_surface [AskSetup]
    [PackageSetup]
    {inputFamily modulus selector schedule readback sealRow provenance localCert stationary
      rationalRead constantSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback sealRow
        provenance localCert bundle pkg ->
      Cont selector schedule stationary ->
        Cont stationary readback rationalRead ->
          Cont rationalRead sealRow constantSeal ->
            hsame rationalRead readback ->
              UnaryHistory stationary ∧ UnaryHistory rationalRead ∧
                UnaryHistory constantSeal ∧ hsame constantSeal sealRow ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet stationaryRoute rationalReadRoute constantSealRoute sameRationalReadback
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, _provenanceUnary,
    selectorRoute, readbackRoute, localCertRoute, sealReturnRoute, provenancePkg⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary selectorRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary readbackRoute
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed selectorUnary scheduleUnary stationaryRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed stationaryUnary readbackUnary rationalReadRoute
  have constantSealUnary : UnaryHistory constantSeal :=
    unary_cont_closed rationalReadUnary sealUnary constantSealRoute
  have constantSameLocalCert : hsame constantSeal localCert :=
    cont_respects_hsame sameRationalReadback (hsame_refl sealRow) constantSealRoute
      localCertRoute
  have swappedLocalCert :
      Cont sealRow readback (append sealRow readback) :=
    cont_intro rfl
  have localCertSameSwapped : hsame localCert (append sealRow readback) :=
    unary_cont_comm readbackUnary sealUnary localCertRoute swappedLocalCert
  have sealReadbackLocalCert : Cont sealRow readback localCert :=
    cont_result_hsame_transport swappedLocalCert (hsame_symm localCertSameSwapped)
  have sealCycle : Cont sealRow (append readback provenance) sealRow := by
    exact sealReturnRoute.trans
      ((congrArg (fun row => append row provenance) sealReadbackLocalCert).trans
        (append_assoc sealRow readback provenance))
  have readbackProvenanceEmpty : hsame (append readback provenance) BHist.Empty :=
    cont_right_unit_unique sealCycle
  have readbackEmpty : hsame readback BHist.Empty :=
    (append_eq_empty_iff.mp readbackProvenanceEmpty).left
  have localCertSameSeal : hsame localCert sealRow := by
    cases readbackEmpty
    exact cont_deterministic sealReadbackLocalCert (cont_right_unit sealRow)
  have constantSameSeal : hsame constantSeal sealRow :=
    hsame_trans constantSameLocalCert localCertSameSeal
  exact
    ⟨stationaryUnary, rationalReadUnary, constantSealUnary, constantSameSeal,
      provenancePkg⟩

theorem RealDiagonalCompletionSourcePacket_constant_rational_handoff [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback sealRow provenance localCert ratRow
      stationaryRead constantSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback sealRow
        provenance localCert bundle pkg ->
      Cont readback ratRow stationaryRead ->
        hsame stationaryRead ratRow ->
          Cont stationaryRead sealRow constantSeal ->
            UnaryHistory ratRow ->
              UnaryHistory stationaryRead ∧ UnaryHistory constantSeal ∧
                hsame stationaryRead ratRow ∧ Cont readback ratRow stationaryRead ∧
                  Cont stationaryRead sealRow constantSeal ∧ PkgSig bundle provenance pkg := by
  intro packet stationaryRoute sameStationary constantRoute ratUnary
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, _provenanceUnary,
    selectorRoute, readbackRoute, _localCertRoute, _sealRoute, provenancePkg⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary selectorRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary readbackRoute
  have stationaryUnary : UnaryHistory stationaryRead :=
    unary_cont_closed readbackUnary ratUnary stationaryRoute
  have constantSealUnary : UnaryHistory constantSeal :=
    unary_cont_closed stationaryUnary sealUnary constantRoute
  exact
    ⟨stationaryUnary, constantSealUnary, sameStationary, stationaryRoute, constantRoute,
      provenancePkg⟩

end BEDC.Derived.RealDiagonalCompletionUp
