import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TriePacket [AskSetup] [PackageSetup]
    (key payload depth branch provenance keyPayloadRoute branchRoute endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧ UnaryHistory branch ∧
    Cont key payload keyPayloadRoute ∧ Cont keyPayloadRoute branch branchRoute ∧
      Cont branchRoute depth endpoint ∧ PkgSig bundle endpoint pkg

theorem TriePacket_carrier_stability [AskSetup] [PackageSetup]
    {key payload depth branch provenance keyPayloadRoute branchRoute endpoint key' payload'
      depth' branch' provenance' keyPayloadRoute' branchRoute' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TriePacket key payload depth branch provenance keyPayloadRoute branchRoute endpoint
        bundle pkg ->
      hsame key key' ->
        hsame payload payload' ->
          hsame depth depth' ->
            hsame branch branch' ->
              Cont key' payload' keyPayloadRoute' ->
                Cont keyPayloadRoute' branch' branchRoute' ->
                  Cont branchRoute' depth' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      TriePacket key' payload' depth' branch' provenance' keyPayloadRoute'
                          branchRoute' endpoint' bundle pkg ∧
                        hsame keyPayloadRoute keyPayloadRoute' ∧
                          hsame branchRoute branchRoute' ∧ hsame endpoint endpoint' := by
  intro packet sameKey samePayload sameDepth sameBranch hKeyPayload hBranchRoute hEndpoint hPkg
  have keyPayloadSame : hsame keyPayloadRoute keyPayloadRoute' :=
    cont_respects_hsame sameKey samePayload packet.right.right.right.right.left hKeyPayload
  have branchRouteSame : hsame branchRoute branchRoute' :=
    cont_respects_hsame keyPayloadSame sameBranch packet.right.right.right.right.right.left
      hBranchRoute
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame branchRouteSame sameDepth packet.right.right.right.right.right.right.left
      hEndpoint
  constructor
  · exact
      And.intro (unary_transport packet.left sameKey)
        (And.intro (unary_transport packet.right.left samePayload)
            (And.intro (unary_transport packet.right.right.left sameDepth)
              (And.intro (unary_transport packet.right.right.right.left sameBranch)
              (And.intro hKeyPayload
                (And.intro hBranchRoute (And.intro hEndpoint hPkg))))))
  · exact And.intro keyPayloadSame (And.intro branchRouteSame endpointSame)

end BEDC.Derived.TrieUp
