import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HodgeBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HodgeBridgeBHistSourcePacket [AskSetup] [PackageSetup]
    (derham cohomology projector bidegree lefschetz readback transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derham ∧ UnaryHistory cohomology ∧ UnaryHistory projector ∧
    UnaryHistory bidegree ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont derham projector readback ∧ Cont readback bidegree lefschetz ∧
        Cont provenance lefschetz endpoint ∧ PkgSig bundle endpoint pkg

theorem HodgeBridgeBHistSourcePacket_source_dependency_surface [AskSetup] [PackageSetup]
    {derham cohomology projector bidegree lefschetz readback transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HodgeBridgeBHistSourcePacket derham cohomology projector bidegree lefschetz readback
        transport provenance endpoint bundle pkg ->
      UnaryHistory derham ∧ UnaryHistory cohomology ∧ UnaryHistory projector ∧
        UnaryHistory bidegree ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
          UnaryHistory readback ∧ UnaryHistory lefschetz ∧ UnaryHistory endpoint ∧
            Cont derham projector readback ∧ Cont readback bidegree lefschetz ∧
              Cont provenance lefschetz endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have projectorUnary : UnaryHistory projector := packet.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.left projectorUnary packet.right.right.right.right.right.right.left
  have bidegreeUnary : UnaryHistory bidegree := packet.right.right.right.left
  have lefschetzUnary : UnaryHistory lefschetz :=
    unary_cont_closed readbackUnary bidegreeUnary
      packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary lefschetzUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, projectorUnary, bidegreeUnary,
      packet.right.right.right.right.left, provenanceUnary, readbackUnary, lefschetzUnary,
      endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.HodgeBridgeUp
