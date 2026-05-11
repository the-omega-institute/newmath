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

end BEDC.Derived.SemidefiniteConeUp
