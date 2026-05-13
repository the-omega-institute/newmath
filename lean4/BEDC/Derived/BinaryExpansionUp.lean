import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BinaryExpansionPacket [AskSetup] [PackageSetup]
    (digits windows approximation regular realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
          Cont transport route provenance ∧ PkgSig bundle provenance pkg

theorem BinaryExpansionPacket_prefix_window_stability [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert digits'
      windows' approximation' regular' realSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      hsame windows windows' -> hsame digits digits' -> hsame regular regular' ->
        Cont windows' digits' approximation' -> Cont approximation' regular' realSeal' ->
          BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport
              route provenance nameCert bundle pkg ∧
            hsame approximation approximation' ∧ hsame realSeal realSeal' := by
  intro packet sameWindows sameDigits sameRegular approximationRow' realSealRow'
  have approximationRow : Cont windows digits approximation :=
    packet.right.right.right.right.right.right.right.right.right.left
  have realSealRow : Cont approximation regular realSeal :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have sameApproximation : hsame approximation approximation' :=
    cont_respects_hsame sameWindows sameDigits approximationRow approximationRow'
  have sameRealSeal : hsame realSeal realSeal' :=
    cont_respects_hsame sameApproximation sameRegular realSealRow realSealRow'
  have transported :
      BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport route
        provenance nameCert bundle pkg :=
    ⟨unary_transport packet.left sameDigits,
      unary_transport packet.right.left sameWindows,
      unary_transport packet.right.right.left sameApproximation,
      unary_transport packet.right.right.right.left sameRegular,
      unary_transport packet.right.right.right.right.left sameRealSeal,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      approximationRow',
      realSealRow',
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right⟩
  exact ⟨transported, sameApproximation, sameRealSeal⟩

theorem BinaryExpansionPacket_regular_handoff_factorization [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      handoffRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      hsame handoffRoute (append windows realSeal) →
        hsame handoffRoute (append windows (append approximation regular)) ∧
          Cont windows digits approximation ∧
            Cont approximation regular realSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet handoffWindowsSeal
  obtain ⟨_digitsUnary, _windowsUnary, _approximationUnary, _regularUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigits,
    approximationRegular, _transportRoute, pkgSig⟩ := packet
  have realSealSame : hsame realSeal (append approximation regular) := approximationRegular
  have handoffSame :
      hsame (append windows realSeal) (append windows (append approximation regular)) :=
    congrArg (fun row => append windows row) realSealSame
  exact ⟨hsame_trans handoffWindowsSeal handoffSame, windowsDigits, approximationRegular, pkgSig⟩

theorem BinaryExpansionPacket_real_readback_boundary [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      Cont regular realSeal realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory windows ∧ UnaryHistory digits ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory realRead ∧
              Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
                Cont regular realSeal realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet regularRealSealRead realReadPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigitsApproximation,
    approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary realSealUnary regularRealSealRead
  exact
    ⟨windowsUnary, digitsUnary, approximationUnary, regularUnary, realSealUnary,
      realReadUnary, windowsDigitsApproximation, approximationRegularRealSeal,
      regularRealSealRead, provenancePkg, realReadPkg⟩

theorem BinaryExpansionPacket_dyadic_ledger_exhaustion [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont digits windows dyadicRead →
        PkgSig bundle dyadicRead pkg →
          UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory dyadicRead ∧
              Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
                Cont digits windows dyadicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet digitsWindowsRead dyadicReadPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigitsApproximation,
    approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed digitsUnary windowsUnary digitsWindowsRead
  exact
    ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
      dyadicReadUnary, windowsDigitsApproximation, approximationRegularRealSeal,
      digitsWindowsRead, provenancePkg, dyadicReadPkg⟩

end BEDC.Derived.BinaryExpansionUp
