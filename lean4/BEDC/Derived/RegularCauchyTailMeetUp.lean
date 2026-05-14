import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailMeetPacket [AskSetup] [PackageSetup]
    (r0 r1 w0 w1 m0 m1 tau q h c l n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
    UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory tau ∧ UnaryHistory q ∧
      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory l ∧ UnaryHistory n ∧
        Cont r0 w0 h ∧ Cont r1 w1 c ∧ Cont m0 m1 tau ∧ Cont tau q l ∧
          PkgSig bundle l pkg

theorem RegularCauchyTailMeetPacket_classifier_stability [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n r0' r1' w0' w1' m0' m1' tau' q' h' c'
      l' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      hsame r0 r0' ->
        hsame r1 r1' ->
          hsame w0 w0' ->
            hsame w1 w1' ->
              hsame m0 m0' ->
                hsame m1 m1' ->
                  hsame q q' ->
                    hsame n n' ->
                      Cont r0' w0' h' ->
                        Cont r1' w1' c' ->
                          Cont m0' m1' tau' ->
                            Cont tau' q' l' ->
                              PkgSig bundle l' pkg ->
                                RegularCauchyTailMeetPacket r0' r1' w0' w1' m0' m1'
                                    tau' q' h' c' l' n' bundle pkg ∧
                                  hsame tau tau' ∧ hsame l l' := by
  intro packet r0Same r1Same w0Same w1Same m0Same m1Same qSame nSame
    r0w0Row r1w1Row m0m1Row tauqRow pkgRow
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, hUnary, cUnary, lUnary, nUnary, r0w0Old, r1w1Old, m0m1Old,
    tauqOld, _pkgOld⟩ := packet
  have r0Unary' : UnaryHistory r0' :=
    unary_transport r0Unary r0Same
  have r1Unary' : UnaryHistory r1' :=
    unary_transport r1Unary r1Same
  have w0Unary' : UnaryHistory w0' :=
    unary_transport w0Unary w0Same
  have w1Unary' : UnaryHistory w1' :=
    unary_transport w1Unary w1Same
  have m0Unary' : UnaryHistory m0' :=
    unary_transport m0Unary m0Same
  have m1Unary' : UnaryHistory m1' :=
    unary_transport m1Unary m1Same
  have tauUnary' : UnaryHistory tau' :=
    unary_cont_closed m0Unary' m1Unary' m0m1Row
  have qUnary' : UnaryHistory q' :=
    unary_transport qUnary qSame
  have hUnary' : UnaryHistory h' :=
    unary_cont_closed r0Unary' w0Unary' r0w0Row
  have cUnary' : UnaryHistory c' :=
    unary_cont_closed r1Unary' w1Unary' r1w1Row
  have lUnary' : UnaryHistory l' :=
    unary_cont_closed tauUnary' qUnary' tauqRow
  have nUnary' : UnaryHistory n' :=
    unary_transport nUnary nSame
  have tauSame : hsame tau tau' :=
    cont_respects_hsame m0Same m1Same m0m1Old m0m1Row
  have lSame : hsame l l' :=
    cont_respects_hsame tauSame qSame tauqOld tauqRow
  exact
    ⟨⟨r0Unary', r1Unary', w0Unary', w1Unary', m0Unary', m1Unary', tauUnary',
        qUnary', hUnary', cUnary', lUnary', nUnary', r0w0Row, r1w1Row, m0m1Row,
        tauqRow, pkgRow⟩,
      tauSame, lSame⟩

theorem RegularCauchyTailMeetPacket_real_seal_handoff [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont l n realSeal ->
        UnaryHistory tau ∧ UnaryHistory q ∧ UnaryHistory l ∧ UnaryHistory n ∧
          UnaryHistory realSeal ∧ Cont m0 m1 tau ∧ Cont tau q l ∧
            Cont l n realSeal ∧ PkgSig bundle l pkg := by
  intro packet sealRoute
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary,
    tauUnary, qUnary, _hUnary, _cUnary, lUnary, nUnary, _r0w0Row, _r1w1Row,
    m0m1Row, tauqRow, pkgRow⟩ := packet
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  exact
    ⟨tauUnary, qUnary, lUnary, nUnary, realSealUnary, m0m1Row, tauqRow,
      sealRoute, pkgRow⟩

theorem RegularCauchyTailMeetPacket_limit_seal_threshold_route [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n limitSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont l n limitSeal ->
        Cont tau limitSeal diagonalRead ->
          PkgSig bundle limitSeal pkg ->
            PkgSig bundle diagonalRead pkg ->
              UnaryHistory tau ∧ UnaryHistory q ∧ UnaryHistory l ∧ UnaryHistory n ∧
                UnaryHistory limitSeal ∧ UnaryHistory diagonalRead ∧ Cont m0 m1 tau ∧
                  Cont tau q l ∧ Cont l n limitSeal ∧
                    Cont tau limitSeal diagonalRead ∧ PkgSig bundle l pkg ∧
                      PkgSig bundle limitSeal pkg ∧ PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet limitRoute diagonalRoute limitPkg diagonalPkg
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary,
    tauUnary, qUnary, _hUnary, _cUnary, lUnary, nUnary, _r0w0Row, _r1w1Row,
    m0m1Row, tauqRow, pkgRow⟩ := packet
  have limitUnary : UnaryHistory limitSeal :=
    unary_cont_closed lUnary nUnary limitRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed tauUnary limitUnary diagonalRoute
  exact
    ⟨tauUnary, qUnary, lUnary, nUnary, limitUnary, diagonalUnary, m0m1Row, tauqRow,
      limitRoute, diagonalRoute, pkgRow, limitPkg, diagonalPkg⟩

theorem RegularCauchyTailMeetPacket_root_window_threshold_coverage [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n rootRead ->
        UnaryHistory r0 /\ UnaryHistory r1 /\ UnaryHistory w0 /\ UnaryHistory w1 /\
          UnaryHistory m0 /\ UnaryHistory m1 /\ UnaryHistory tau /\ UnaryHistory q /\
            UnaryHistory rootRead /\ Cont r0 w0 h /\ Cont r1 w1 c /\
              Cont m0 m1 tau /\ Cont tau q l /\ Cont q n rootRead /\
                PkgSig bundle l pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, _lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary, qUnary,
      rootUnary, r0w0Row, r1w1Row, m0m1Row, tauqRow, rootRoute, pkgRow⟩

theorem RegularCauchyTailMeetPacket_root_downstream_window_exhaustion [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg →
      Cont q n rootRead →
        UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
          UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory l ∧ UnaryHistory rootRead ∧
            Cont r0 w0 h ∧ Cont r1 w1 c ∧ Cont tau q l ∧ Cont q n rootRead ∧
              PkgSig bundle l pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, _m0Unary, _m1Unary, _tauUnary,
    qUnary, hUnary, cUnary, lUnary, nUnary, r0w0Row, r1w1Row, _m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, hUnary, cUnary, lUnary, rootUnary,
      r0w0Row, r1w1Row, tauqRow, rootRoute, pkgRow⟩

theorem RegularCauchyTailMeetPacket_root_downstream_threshold_stability [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n r0' r1' w0' w1' m0' m1' tau' q' h' c'
      l' n' rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      hsame r0 r0' ->
        hsame r1 r1' ->
          hsame w0 w0' ->
            hsame w1 w1' ->
              hsame m0 m0' ->
                hsame m1 m1' ->
                  hsame q q' ->
                    hsame n n' ->
                      Cont r0' w0' h' ->
                        Cont r1' w1' c' ->
                          Cont m0' m1' tau' ->
                            Cont tau' q' l' ->
                              Cont q' n' rootRead ->
                                PkgSig bundle l' pkg ->
                                  RegularCauchyTailMeetPacket r0' r1' w0' w1'
                                      m0' m1' tau' q' h' c' l' n' bundle pkg ∧
                                    hsame tau tau' ∧ hsame l l' ∧
                                      UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet r0Same r1Same w0Same w1Same m0Same m1Same qSame nSame
    r0w0Row r1w1Row m0m1Row tauqRow rootRoute pkgRow
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, _tauUnary,
    qUnary, _hUnary, _cUnary, _lUnary, nUnary, r0w0Old, r1w1Old, m0m1Old,
    tauqOld, _pkgOld⟩ := packet
  have r0Unary' : UnaryHistory r0' :=
    unary_transport r0Unary r0Same
  have r1Unary' : UnaryHistory r1' :=
    unary_transport r1Unary r1Same
  have w0Unary' : UnaryHistory w0' :=
    unary_transport w0Unary w0Same
  have w1Unary' : UnaryHistory w1' :=
    unary_transport w1Unary w1Same
  have m0Unary' : UnaryHistory m0' :=
    unary_transport m0Unary m0Same
  have m1Unary' : UnaryHistory m1' :=
    unary_transport m1Unary m1Same
  have tauUnary' : UnaryHistory tau' :=
    unary_cont_closed m0Unary' m1Unary' m0m1Row
  have qUnary' : UnaryHistory q' :=
    unary_transport qUnary qSame
  have hUnary' : UnaryHistory h' :=
    unary_cont_closed r0Unary' w0Unary' r0w0Row
  have cUnary' : UnaryHistory c' :=
    unary_cont_closed r1Unary' w1Unary' r1w1Row
  have lUnary' : UnaryHistory l' :=
    unary_cont_closed tauUnary' qUnary' tauqRow
  have nUnary' : UnaryHistory n' :=
    unary_transport nUnary nSame
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary' nUnary' rootRoute
  have tauSame : hsame tau tau' :=
    cont_respects_hsame m0Same m1Same m0m1Old m0m1Row
  have lSame : hsame l l' :=
    cont_respects_hsame tauSame qSame tauqOld tauqRow
  exact
    ⟨⟨r0Unary', r1Unary', w0Unary', w1Unary', m0Unary', m1Unary', tauUnary',
        qUnary', hUnary', cUnary', lUnary', nUnary', r0w0Row, r1w1Row, m0m1Row,
        tauqRow, pkgRow⟩,
      tauSame, lSame, rootUnary⟩

theorem RegularCauchyTailMeetFormalHandoffLeanTarget [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead realSeal budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n rootRead ->
        Cont l n realSeal ->
          Cont rootRead realSeal budgetRead ->
            UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
              UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory tau ∧ UnaryHistory q ∧
                UnaryHistory l ∧ UnaryHistory n ∧ UnaryHistory rootRead ∧
                  UnaryHistory realSeal ∧ UnaryHistory budgetRead ∧ Cont r0 w0 h ∧
                    Cont r1 w1 c ∧ Cont m0 m1 tau ∧ Cont tau q l ∧
                      Cont q n rootRead ∧ Cont l n realSeal ∧
                        Cont rootRead realSeal budgetRead ∧ PkgSig bundle l pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute sealRoute budgetRoute
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed rootUnary realSealUnary budgetRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary, qUnary,
      lUnary, nUnary, rootUnary, realSealUnary, budgetUnary, r0w0Row, r1w1Row,
      m0m1Row, tauqRow, rootRoute, sealRoute, budgetRoute, pkgRow⟩

theorem RegularCauchyTailMeetPacket_selector_budget_public_route [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n selectorWindow selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n selectorWindow ->
        Cont selectorWindow tau selectorRead ->
          PkgSig bundle selectorRead pkg ->
            UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧ UnaryHistory w1 ∧
              UnaryHistory tau ∧ UnaryHistory selectorWindow ∧
                UnaryHistory selectorRead ∧ Cont r0 w0 h ∧ Cont r1 w1 c ∧
                  Cont q n selectorWindow ∧ Cont selectorWindow tau selectorRead ∧
                    PkgSig bundle l pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet selectorWindowRoute selectorReadRoute selectorReadPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, _m0Unary, _m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, _lUnary, nUnary, r0w0Row, r1w1Row, _m0m1Row,
    _tauqRow, pkgRow⟩ := packet
  have selectorWindowUnary : UnaryHistory selectorWindow :=
    unary_cont_closed qUnary nUnary selectorWindowRoute
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed selectorWindowUnary tauUnary selectorReadRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, tauUnary, selectorWindowUnary,
      selectorReadUnary, r0w0Row, r1w1Row, selectorWindowRoute, selectorReadRoute,
      pkgRow, selectorReadPkg⟩

theorem RegularCauchyTailMeetPacket_public_shared_threshold_certificate [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead realSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n rootRead ->
        Cont l n realSeal ->
          Cont tau realSeal diagonalRead ->
            PkgSig bundle realSeal pkg ->
              PkgSig bundle diagonalRead pkg ->
                UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧
                  UnaryHistory w1 ∧ UnaryHistory tau ∧ UnaryHistory q ∧
                    UnaryHistory rootRead ∧ UnaryHistory realSeal ∧
                      UnaryHistory diagonalRead ∧ Cont r0 w0 h ∧ Cont r1 w1 c ∧
                        Cont m0 m1 tau ∧ Cont tau q l ∧ Cont q n rootRead ∧
                          Cont l n realSeal ∧ Cont tau realSeal diagonalRead ∧
                            PkgSig bundle l pkg ∧ PkgSig bundle realSeal pkg ∧
                              PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute sealRoute diagonalRoute sealPkg diagonalPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, _m0Unary, _m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed tauUnary realSealUnary diagonalRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, tauUnary, qUnary, rootUnary,
      realSealUnary, diagonalUnary, r0w0Row, r1w1Row, m0m1Row, tauqRow,
      rootRoute, sealRoute, diagonalRoute, pkgRow, sealPkg, diagonalPkg⟩

theorem RegularCauchyTailMeetPacket_root_downstream_seal_route [AskSetup]
    [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead realSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n rootRead ->
        Cont l n realSeal ->
          Cont rootRead realSeal sealRead ->
            PkgSig bundle realSeal pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧
                  UnaryHistory w1 ∧ UnaryHistory m0 ∧ UnaryHistory m1 ∧
                    UnaryHistory tau ∧ UnaryHistory q ∧ UnaryHistory l ∧
                      UnaryHistory n ∧ UnaryHistory rootRead ∧
                        UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
                          Cont r0 w0 h ∧ Cont r1 w1 c ∧ Cont m0 m1 tau ∧
                            Cont tau q l ∧ Cont q n rootRead ∧
                              Cont l n realSeal ∧ Cont rootRead realSeal sealRead ∧
                                PkgSig bundle l pkg ∧ PkgSig bundle realSeal pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute sealRoute sealReadRoute sealPkg sealReadPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary realSealUnary sealReadRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, m0Unary, m1Unary, tauUnary, qUnary,
      lUnary, nUnary, rootUnary, realSealUnary, sealReadUnary, r0w0Row, r1w1Row,
      m0m1Row, tauqRow, rootRoute, sealRoute, sealReadRoute, pkgRow, sealPkg,
      sealReadPkg⟩

theorem RegularCauchyTailMeetPacket_selector_budget_route_lock [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n rootRead selectorBudget sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont q n rootRead ->
        Cont rootRead tau selectorBudget ->
          Cont selectorBudget l sealRead ->
            PkgSig bundle selectorBudget pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory w0 ∧
                  UnaryHistory w1 ∧ UnaryHistory tau ∧ UnaryHistory q ∧
                    UnaryHistory l ∧ UnaryHistory rootRead ∧
                      UnaryHistory selectorBudget ∧ UnaryHistory sealRead ∧
                        Cont r0 w0 h ∧ Cont r1 w1 c ∧ Cont m0 m1 tau ∧
                          Cont tau q l ∧ Cont q n rootRead ∧
                            Cont rootRead tau selectorBudget ∧
                              Cont selectorBudget l sealRead ∧ PkgSig bundle l pkg ∧
                                PkgSig bundle selectorBudget pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute selectorRoute sealReadRoute selectorPkg sealReadPkg
  obtain ⟨r0Unary, r1Unary, w0Unary, w1Unary, _m0Unary, _m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, lUnary, nUnary, r0w0Row, r1w1Row, m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed qUnary nUnary rootRoute
  have selectorUnary : UnaryHistory selectorBudget :=
    unary_cont_closed rootUnary tauUnary selectorRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorUnary lUnary sealReadRoute
  exact
    ⟨r0Unary, r1Unary, w0Unary, w1Unary, tauUnary, qUnary, lUnary, rootUnary,
      selectorUnary, sealReadUnary, r0w0Row, r1w1Row, m0m1Row, tauqRow, rootRoute,
      selectorRoute, sealReadRoute, pkgRow, selectorPkg, sealReadPkg⟩

end BEDC.Derived.RegularCauchyTailMeetUp
