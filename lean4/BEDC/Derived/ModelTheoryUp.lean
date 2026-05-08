import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModelTheoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModelTheoryBHistStructurePacket [AskSetup] [PackageSetup]
    (firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory firstOrder ∧
    UnaryHistory structureRow ∧
      UnaryHistory satisfaction ∧
        UnaryHistory elementary ∧
          Cont firstOrder structureRow valuation ∧
            Cont valuation satisfaction provenance ∧
              Cont provenance elementary endpoint ∧
                PkgSig bundle endpoint pkg

theorem ModelTheoryBHistStructurePacket_firstorder_dependency_surface [AskSetup]
    [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
      provenance endpoint bundle pkg ->
        UnaryHistory firstOrder ∧
          UnaryHistory structureRow ∧
            hsame valuation (append firstOrder structureRow) ∧
              hsame provenance (append valuation satisfaction) ∧
                hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact
    And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right))))

theorem ModelTheoryBHistStructurePacket_elementary_transport [AskSetup] [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint valuation'
      satisfaction' elementary' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
        provenance endpoint bundle pkg ->
      hsame satisfaction satisfaction' ->
        hsame elementary elementary' ->
          Cont firstOrder structureRow valuation' ->
            Cont valuation' satisfaction' provenance' ->
              Cont provenance' elementary' endpoint' ->
                ModelTheoryBHistStructurePacket firstOrder structureRow valuation' satisfaction'
                    elementary' provenance' endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  intro packet sameSatisfaction sameElementary valuationCont' provenanceCont' endpointCont'
  have satisfactionUnary' : UnaryHistory satisfaction' :=
    unary_transport packet.right.right.left sameSatisfaction
  have elementaryUnary' : UnaryHistory elementary' :=
    unary_transport packet.right.right.right.left sameElementary
  have sameValuation : hsame valuation valuation' :=
    cont_respects_hsame (hsame_refl firstOrder) (hsame_refl structureRow)
      packet.right.right.right.right.left valuationCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameValuation sameSatisfaction
      packet.right.right.right.right.right.left provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameElementary
      packet.right.right.right.right.right.right.left endpointCont'
  have pkgSig : PkgSig bundle endpoint' pkg := by
    cases sameEndpoint
    exact packet.right.right.right.right.right.right.right
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro satisfactionUnary'
          (And.intro elementaryUnary'
            (And.intro valuationCont'
              (And.intro provenanceCont' (And.intro endpointCont' pkgSig)))))))
    sameEndpoint

theorem ModelTheoryBHistStructurePacket_satisfaction_exactness_scope [AskSetup]
    [PackageSetup]
    {firstOrder structureRow valuation satisfaction elementary provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelTheoryBHistStructurePacket firstOrder structureRow valuation satisfaction elementary
      provenance endpoint bundle pkg ->
        UnaryHistory valuation ∧ UnaryHistory provenance ∧
          hsame valuation (append firstOrder structureRow) ∧
            hsame provenance (append valuation satisfaction) ∧
              hsame endpoint (append provenance elementary) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have valuationUnary : UnaryHistory valuation :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed valuationUnary packet.right.right.left
      packet.right.right.right.right.right.left
  exact And.intro valuationUnary
    (And.intro provenanceUnary
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.left
            packet.right.right.right.right.right.right.right))))

end BEDC.Derived.ModelTheoryUp
