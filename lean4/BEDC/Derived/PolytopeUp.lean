import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolytopeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PolytopeBHistFacePacket
    (convex fin halfspace vertex edge face incidence ledger provenance : BHist) : Prop :=
  UnaryHistory convex ∧ UnaryHistory fin ∧ UnaryHistory halfspace ∧
    UnaryHistory vertex ∧ UnaryHistory edge ∧ UnaryHistory face ∧
      Cont halfspace vertex incidence ∧ Cont incidence edge ledger ∧ hsame provenance face

theorem PolytopeBHistFacePacket_hsame_stability
    {convex fin halfspace vertex edge face incidence ledger provenance : BHist}
    {convexPrime finPrime halfspacePrime vertexPrime edgePrime facePrime incidencePrime
      ledgerPrime provenancePrime : BHist} :
    PolytopeBHistFacePacket convex fin halfspace vertex edge face incidence ledger provenance ->
      hsame convexPrime convex ->
        hsame finPrime fin ->
          hsame halfspacePrime halfspace ->
            hsame vertexPrime vertex ->
              hsame edgePrime edge ->
                hsame facePrime face ->
                  hsame provenancePrime provenance ->
                    Cont halfspacePrime vertexPrime incidencePrime ->
                      Cont incidencePrime edgePrime ledgerPrime ->
                        PolytopeBHistFacePacket convexPrime finPrime halfspacePrime
                          vertexPrime edgePrime facePrime incidencePrime ledgerPrime
                          provenancePrime ∧
                          hsame incidence incidencePrime ∧ hsame ledger ledgerPrime := by
  intro packet sameConvex sameFin sameHalfspace sameVertex sameEdge sameFace sameProvenance
    incidencePrimeCont ledgerPrimeCont
  have convexPrimeUnary : UnaryHistory convexPrime :=
    unary_transport packet.left (hsame_symm sameConvex)
  have finPrimeUnary : UnaryHistory finPrime :=
    unary_transport packet.right.left (hsame_symm sameFin)
  have halfspacePrimeUnary : UnaryHistory halfspacePrime :=
    unary_transport packet.right.right.left (hsame_symm sameHalfspace)
  have vertexPrimeUnary : UnaryHistory vertexPrime :=
    unary_transport packet.right.right.right.left (hsame_symm sameVertex)
  have edgePrimeUnary : UnaryHistory edgePrime :=
    unary_transport packet.right.right.right.right.left (hsame_symm sameEdge)
  have facePrimeUnary : UnaryHistory facePrime :=
    unary_transport packet.right.right.right.right.right.left (hsame_symm sameFace)
  have sameIncidence : hsame incidence incidencePrime :=
    cont_respects_hsame (hsame_symm sameHalfspace) (hsame_symm sameVertex)
      packet.right.right.right.right.right.right.left incidencePrimeCont
  have sameLedger : hsame ledger ledgerPrime :=
    cont_respects_hsame sameIncidence (hsame_symm sameEdge)
      packet.right.right.right.right.right.right.right.left ledgerPrimeCont
  have sameProvenanceFace : hsame provenancePrime facePrime :=
    hsame_trans sameProvenance
      (hsame_trans packet.right.right.right.right.right.right.right.right
        (hsame_symm sameFace))
  exact And.intro
    (And.intro convexPrimeUnary
      (And.intro finPrimeUnary
        (And.intro halfspacePrimeUnary
          (And.intro vertexPrimeUnary
            (And.intro edgePrimeUnary
              (And.intro facePrimeUnary
                (And.intro incidencePrimeCont
                  (And.intro ledgerPrimeCont sameProvenanceFace))))))))
    (And.intro sameIncidence sameLedger)

end BEDC.Derived.PolytopeUp
