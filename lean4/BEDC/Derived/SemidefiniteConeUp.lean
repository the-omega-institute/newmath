import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SemidefiniteConeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SemidefiniteConePacket [AskSetup] [PackageSetup]
    (matrix vector convexLedger bilinearPairing nonnegative provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory matrix ∧ UnaryHistory vector ∧ UnaryHistory convexLedger ∧
    UnaryHistory bilinearPairing ∧ UnaryHistory nonnegative ∧ UnaryHistory provenance ∧
      UnaryHistory endpoint ∧ Cont matrix vector bilinearPairing ∧
        Cont convexLedger bilinearPairing nonnegative ∧
          Cont bilinearPairing nonnegative endpoint ∧ PkgSig bundle endpoint pkg

theorem SemidefiniteConePacket_carrier_stability [AskSetup] [PackageSetup]
    {matrix vector convexLedger bilinearPairing nonnegative provenance endpoint matrix' vector'
      convexLedger' bilinearPairing' nonnegative' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemidefiniteConePacket matrix vector convexLedger bilinearPairing nonnegative provenance
        endpoint bundle pkg ->
      hsame matrix matrix' ->
        hsame vector vector' ->
          hsame convexLedger convexLedger' ->
            hsame provenance provenance' ->
              Cont matrix' vector' bilinearPairing' ->
                Cont convexLedger' bilinearPairing' nonnegative' ->
                  Cont bilinearPairing' nonnegative' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      SemidefiniteConePacket matrix' vector' convexLedger' bilinearPairing'
                          nonnegative' provenance' endpoint' bundle pkg ∧
                        hsame bilinearPairing bilinearPairing' ∧
                          hsame nonnegative nonnegative' ∧ hsame endpoint endpoint' := by
  intro packet sameMatrix sameVector sameConvex sameProvenance bilinearRow'
    nonnegativeRow' endpointRow' endpointPkg'
  obtain ⟨matrixUnary, vectorUnary, convexUnary, _bilinearUnary, _nonnegativeUnary,
    provenanceUnary, _endpointUnary, bilinearRow, nonnegativeRow, endpointRow,
    _endpointPkg⟩ := packet
  have matrixUnary' : UnaryHistory matrix' :=
    unary_transport matrixUnary sameMatrix
  have vectorUnary' : UnaryHistory vector' :=
    unary_transport vectorUnary sameVector
  have convexUnary' : UnaryHistory convexLedger' :=
    unary_transport convexUnary sameConvex
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have bilinearUnary' : UnaryHistory bilinearPairing' :=
    unary_cont_closed matrixUnary' vectorUnary' bilinearRow'
  have sameBilinear : hsame bilinearPairing bilinearPairing' :=
    cont_respects_hsame sameMatrix sameVector bilinearRow bilinearRow'
  have nonnegativeUnary' : UnaryHistory nonnegative' :=
    unary_cont_closed convexUnary' bilinearUnary' nonnegativeRow'
  have sameNonnegative : hsame nonnegative nonnegative' :=
    cont_respects_hsame sameConvex sameBilinear nonnegativeRow nonnegativeRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed bilinearUnary' nonnegativeUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameBilinear sameNonnegative endpointRow endpointRow'
  exact And.intro
    (And.intro matrixUnary'
      (And.intro vectorUnary'
        (And.intro convexUnary'
          (And.intro bilinearUnary'
            (And.intro nonnegativeUnary'
              (And.intro provenanceUnary'
                (And.intro endpointUnary'
                  (And.intro bilinearRow'
                    (And.intro nonnegativeRow'
                      (And.intro endpointRow' endpointPkg'))))))))))
    (And.intro sameBilinear (And.intro sameNonnegative sameEndpoint))

theorem SemidefiniteConePacket_cone_operation_ledger [AskSetup] [PackageSetup]
    {matrix0 vector0 convexLedger0 bilinearPairing0 nonnegative0 provenance0 endpoint0
      matrix1 vector1 convexLedger1 bilinearPairing1 nonnegative1 provenance1 endpoint1
      matrixSum convexSum bilinearSum nonnegativeSum endpointSum : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemidefiniteConePacket matrix0 vector0 convexLedger0 bilinearPairing0 nonnegative0
        provenance0 endpoint0 bundle pkg ->
      SemidefiniteConePacket matrix1 vector1 convexLedger1 bilinearPairing1 nonnegative1
          provenance1 endpoint1 bundle pkg ->
        hsame vector0 vector1 ->
          hsame provenance0 provenance1 ->
            Cont matrix0 matrix1 matrixSum ->
              Cont convexLedger0 convexLedger1 convexSum ->
                Cont matrixSum vector0 bilinearSum ->
                  Cont convexSum bilinearSum nonnegativeSum ->
                    Cont bilinearSum nonnegativeSum endpointSum ->
                      PkgSig bundle endpointSum pkg ->
                        SemidefiniteConePacket matrixSum vector0 convexSum bilinearSum
                            nonnegativeSum provenance0 endpointSum bundle pkg ∧
                          hsame matrixSum (append matrix0 matrix1) ∧
                            hsame convexSum (append convexLedger0 convexLedger1) ∧
                              hsame endpointSum (append bilinearSum nonnegativeSum) := by
  intro packet0 packet1 _sameVector _sameProvenance matrixRow convexRow bilinearRow
    nonnegativeRow endpointRow endpointSig
  obtain ⟨matrixUnary0, vectorUnary0, convexUnary0, _bilinearUnary0, _nonnegativeUnary0,
    provenanceUnary0, _endpointUnary0, _bilinearRow0, _nonnegativeRow0, _endpointRow0,
    _endpointSig0⟩ := packet0
  obtain ⟨matrixUnary1, _vectorUnary1, convexUnary1, _bilinearUnary1, _nonnegativeUnary1,
    _provenanceUnary1, _endpointUnary1, _bilinearRow1, _nonnegativeRow1, _endpointRow1,
    _endpointSig1⟩ := packet1
  have matrixSumUnary : UnaryHistory matrixSum :=
    unary_cont_closed matrixUnary0 matrixUnary1 matrixRow
  have convexSumUnary : UnaryHistory convexSum :=
    unary_cont_closed convexUnary0 convexUnary1 convexRow
  have bilinearSumUnary : UnaryHistory bilinearSum :=
    unary_cont_closed matrixSumUnary vectorUnary0 bilinearRow
  have nonnegativeSumUnary : UnaryHistory nonnegativeSum :=
    unary_cont_closed convexSumUnary bilinearSumUnary nonnegativeRow
  have endpointSumUnary : UnaryHistory endpointSum :=
    unary_cont_closed bilinearSumUnary nonnegativeSumUnary endpointRow
  exact
    ⟨⟨matrixSumUnary, vectorUnary0, convexSumUnary, bilinearSumUnary, nonnegativeSumUnary,
        provenanceUnary0, endpointSumUnary, bilinearRow, nonnegativeRow, endpointRow,
        endpointSig⟩,
      matrixRow,
      convexRow,
      endpointRow⟩

theorem SemidefiniteConePacket_dual_pairing_empty_boundary [AskSetup] [PackageSetup]
    {matrix vector convexLedger bilinearPairing nonnegative provenance endpoint consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemidefiniteConePacket matrix vector convexLedger bilinearPairing nonnegative provenance
        endpoint bundle pkg ->
      Cont endpoint provenance consumerRow ->
        hsame consumerRow BHist.Empty ->
          hsame endpoint BHist.Empty ∧ hsame provenance BHist.Empty := by
  intro _packet consumerRowCont consumerRowEmpty
  have appendedEmpty : append endpoint provenance = BHist.Empty := by
    cases consumerRowCont
    exact consumerRowEmpty
  have parts : endpoint = BHist.Empty ∧ provenance = BHist.Empty :=
    append_eq_empty_iff.mp appendedEmpty
  exact And.intro parts.left parts.right

end BEDC.Derived.SemidefiniteConeUp
