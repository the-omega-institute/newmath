import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InfCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def InfCatBHistSourcePacket [AskSetup] [PackageSetup]
    (simplicial category horn lift provenance transport : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory simplicial ∧ UnaryHistory category ∧ UnaryHistory horn ∧
    UnaryHistory lift ∧ UnaryHistory provenance ∧ Cont simplicial horn lift ∧
      Cont provenance lift transport ∧ PkgSig bundle transport pkg

theorem InfCatBHistSourcePacket_inner_horn_ledger_boundary [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      UnaryHistory simplicial ∧ UnaryHistory horn ∧ UnaryHistory lift ∧
        UnaryHistory provenance ∧ UnaryHistory transport ∧ Cont simplicial horn lift ∧
          Cont provenance lift transport ∧ hsame lift (append simplicial horn) ∧
            hsame transport (append provenance lift) ∧ PkgSig bundle transport pkg := by
  intro packet
  have simplicialUnary : UnaryHistory simplicial := packet.left
  have hornUnary : UnaryHistory horn := packet.right.right.left
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have simplicialHornLift : Cont simplicial horn lift :=
    packet.right.right.right.right.right.left
  have provenanceLiftTransport : Cont provenance lift transport :=
    packet.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceLiftTransport
  exact And.intro simplicialUnary
    (And.intro hornUnary
      (And.intro liftUnary
        (And.intro provenanceUnary
          (And.intro transportUnary
            (And.intro simplicialHornLift
              (And.intro provenanceLiftTransport
                (And.intro simplicialHornLift
                  (And.intro provenanceLiftTransport
                    packet.right.right.right.right.right.right.right))))))))

theorem InfCatQuasicategoryClassifierSurface_transport [AskSetup] [PackageSetup]
    {category horn lifting provenance categoryHorn hornLifting endpoint category' horn'
      lifting' provenance' categoryHorn' hornLifting' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory category -> UnaryHistory horn -> UnaryHistory lifting ->
      UnaryHistory provenance -> Cont category horn categoryHorn ->
        Cont categoryHorn lifting hornLifting -> Cont provenance hornLifting endpoint ->
          PkgSig bundle endpoint pkg -> hsame category category' -> hsame horn horn' ->
            hsame lifting lifting' -> hsame provenance provenance' ->
              Cont category' horn' categoryHorn' ->
                Cont categoryHorn' lifting' hornLifting' ->
                  Cont provenance' hornLifting' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      UnaryHistory categoryHorn' ∧ UnaryHistory hornLifting' ∧
                        hsame categoryHorn categoryHorn' ∧
                          hsame hornLifting hornLifting' ∧ hsame endpoint endpoint' ∧
                            PkgSig bundle endpoint' pkg := by
  intro categoryUnary hornUnary liftingUnary _provenanceUnary categoryHornCont hornLiftingCont
    endpointCont _pkgSig sameCategory sameHorn sameLifting sameProvenance categoryHornCont'
    hornLiftingCont' endpointCont' pkgSig'
  have categoryUnary' : UnaryHistory category' :=
    unary_transport categoryUnary sameCategory
  have hornUnary' : UnaryHistory horn' :=
    unary_transport hornUnary sameHorn
  have liftingUnary' : UnaryHistory lifting' :=
    unary_transport liftingUnary sameLifting
  have categoryHornUnary' : UnaryHistory categoryHorn' :=
    unary_cont_closed categoryUnary' hornUnary' categoryHornCont'
  have sameCategoryHorn : hsame categoryHorn categoryHorn' :=
    cont_respects_hsame sameCategory sameHorn categoryHornCont categoryHornCont'
  have hornLiftingUnary' : UnaryHistory hornLifting' :=
    unary_cont_closed categoryHornUnary' liftingUnary' hornLiftingCont'
  have sameHornLifting : hsame hornLifting hornLifting' :=
    cont_respects_hsame sameCategoryHorn sameLifting hornLiftingCont hornLiftingCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameHornLifting endpointCont endpointCont'
  exact
    ⟨categoryHornUnary', hornLiftingUnary', sameCategoryHorn, sameHornLifting,
      sameEndpoint, pkgSig'⟩

end BEDC.Derived.InfCatUp
