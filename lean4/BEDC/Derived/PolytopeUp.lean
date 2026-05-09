import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary.Closure

namespace BEDC.Derived.PolytopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PolytopeBHistFacePacket [AskSetup] [PackageSetup]
    (convex finset halfspaces vertices edges faces ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory convex ∧
    UnaryHistory finset ∧
      UnaryHistory halfspaces ∧
        UnaryHistory vertices ∧
          UnaryHistory edges ∧
            UnaryHistory faces ∧
              UnaryHistory ledger ∧
                UnaryHistory provenance ∧
                  UnaryHistory endpoint ∧
                    Cont halfspaces vertices edges ∧
                      Cont edges faces ledger ∧
                        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem PolytopeBHistFacePacket_halfspace_face_carrier_stability [AskSetup]
    [PackageSetup]
    {convex finset halfspaces vertices edges faces ledger provenance endpoint halfspaces'
      vertices' edges' faces' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolytopeBHistFacePacket convex finset halfspaces vertices edges faces ledger provenance
        endpoint bundle pkg ->
      hsame halfspaces halfspaces' ->
        hsame vertices vertices' ->
          hsame edges edges' ->
            hsame faces faces' ->
              Cont halfspaces' vertices' edges' ->
                Cont edges' faces' ledger' ->
                  Cont provenance ledger' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      PolytopeBHistFacePacket convex finset halfspaces' vertices' edges' faces'
                          ledger' provenance endpoint' bundle pkg ∧
                        hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameHalfspaces sameVertices sameEdges sameFaces edgeCont ledgerCont endpointCont
    endpointPkg
  cases packet with
  | intro convexUnary packet =>
      cases packet with
      | intro finsetUnary packet =>
          cases packet with
          | intro halfspacesUnary0 packet =>
              cases packet with
              | intro verticesUnary0 packet =>
                  cases packet with
                  | intro _edgesUnary0 packet =>
                      cases packet with
                      | intro facesUnary0 packet =>
                          cases packet with
                          | intro _ledgerUnary0 packet =>
                              cases packet with
                              | intro provenanceUnary packet =>
                                  cases packet with
                                  | intro _endpointUnary0 packet =>
                                      cases packet with
                                      | intro _edgeCont0 packet =>
                                          cases packet with
                                          | intro ledgerCont0 packet =>
                                              cases packet with
                                              | intro endpointCont0 _endpointPkg0 =>
                                                  have halfspacesUnary :
                                                      UnaryHistory halfspaces' :=
                                                    unary_transport halfspacesUnary0 sameHalfspaces
                                                  have verticesUnary :
                                                      UnaryHistory vertices' :=
                                                    unary_transport verticesUnary0 sameVertices
                                                  have edgesUnary : UnaryHistory edges' :=
                                                    unary_cont_closed halfspacesUnary verticesUnary
                                                      edgeCont
                                                  have facesUnary : UnaryHistory faces' :=
                                                    unary_transport facesUnary0 sameFaces
                                                  have ledgerUnary : UnaryHistory ledger' :=
                                                    unary_cont_closed edgesUnary facesUnary
                                                      ledgerCont
                                                  have endpointUnary : UnaryHistory endpoint' :=
                                                    unary_cont_closed provenanceUnary ledgerUnary
                                                      endpointCont
                                                  have sameLedger : hsame ledger ledger' :=
                                                    cont_respects_hsame sameEdges sameFaces
                                                      ledgerCont0 ledgerCont
                                                  have sameEndpoint : hsame endpoint endpoint' :=
                                                    cont_respects_hsame (hsame_refl provenance)
                                                      sameLedger endpointCont0 endpointCont
                                                  exact And.intro
                                                    (And.intro convexUnary
                                                      (And.intro finsetUnary
                                                        (And.intro halfspacesUnary
                                                          (And.intro verticesUnary
                                                            (And.intro edgesUnary
                                                              (And.intro facesUnary
                                                                (And.intro ledgerUnary
                                                                  (And.intro provenanceUnary
                                                                    (And.intro endpointUnary
                                                                      (And.intro edgeCont
                                                                        (And.intro ledgerCont
                                                                          (And.intro endpointCont
                                                                            endpointPkg))))))))))))
                                                    (And.intro sameLedger sameEndpoint)

theorem PolytopeBHistFacePacket_vertex_edge_ledger_readback [AskSetup] [PackageSetup]
    {convex finset halfspaces vertices edges faces ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolytopeBHistFacePacket convex finset halfspaces vertices edges faces ledger provenance
        endpoint bundle pkg ->
      UnaryHistory vertices ∧
        UnaryHistory edges ∧
          UnaryHistory faces ∧
            Cont halfspaces vertices edges ∧
              Cont edges faces ledger ∧
                hsame ledger (append edges faces) ∧
                  hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  cases packet with
  | intro _convexUnary packet =>
      cases packet with
      | intro _finsetUnary packet =>
          cases packet with
          | intro _halfspacesUnary packet =>
              cases packet with
              | intro verticesUnary packet =>
                  cases packet with
                  | intro edgesUnary packet =>
                      cases packet with
                      | intro facesUnary packet =>
                          cases packet with
                          | intro _ledgerUnary packet =>
                              cases packet with
                              | intro _provenanceUnary packet =>
                                  cases packet with
                                  | intro _endpointUnary packet =>
                                      cases packet with
                                      | intro edgeCont packet =>
                                          cases packet with
                                          | intro ledgerCont packet =>
                                              cases packet with
                                              | intro endpointCont endpointPkg =>
                                                  exact And.intro verticesUnary
                                                    (And.intro edgesUnary
                                                      (And.intro facesUnary
                                                        (And.intro edgeCont
                                                          (And.intro ledgerCont
                                                            (And.intro ledgerCont
                                                              (And.intro endpointCont
                                                                endpointPkg))))))

theorem PolytopeBHistFacePacket_obligation_boundary_exhaustion [AskSetup] [PackageSetup]
    {convex finset halfspaces vertices edges faces ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolytopeBHistFacePacket convex finset halfspaces vertices edges faces ledger provenance
        endpoint bundle pkg ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint) hsame ∧
        UnaryHistory halfspaces ∧ UnaryHistory vertices ∧ UnaryHistory edges ∧
          UnaryHistory faces ∧ Cont halfspaces vertices edges ∧ Cont edges faces ledger ∧
            Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have readback := PolytopeBHistFacePacket_vertex_edge_ledger_readback packet
  have endpointSelf : hsame endpoint endpoint :=
    hsame_refl endpoint
  have halfspacesUnary : UnaryHistory halfspaces :=
    packet.right.right.left
  have endpointCont : Cont provenance ledger endpoint :=
    readback.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrierH
      exact carrierH
    ledger_sound := by
      intro h carrierH
      exact carrierH
  }
  exact And.intro cert
    (And.intro halfspacesUnary
      (And.intro readback.left
        (And.intro readback.right.left
          (And.intro readback.right.right.left
            (And.intro readback.right.right.right.left
              (And.intro readback.right.right.right.right.left
                (And.intro endpointCont
                  readback.right.right.right.right.right.right.right)))))))

end BEDC.Derived.PolytopeUp
