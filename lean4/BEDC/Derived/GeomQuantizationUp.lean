import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GeomQuantizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeomQuantizationBHistSourcePacket [AskSetup] [PackageSetup]
    (symplectic hilbert line polarisation metaplectic readback transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory line ∧
    UnaryHistory polarisation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont symplectic line readback ∧ Cont readback polarisation metaplectic ∧
        Cont provenance metaplectic endpoint ∧ PkgSig bundle endpoint pkg

theorem GeomQuantizationBHistSourcePacket_source_dependency_surface
    [AskSetup] [PackageSetup]
    {symplectic hilbert line polarisation metaplectic readback transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeomQuantizationBHistSourcePacket symplectic hilbert line polarisation metaplectic
        readback transport provenance endpoint bundle pkg ->
      UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory line ∧
        UnaryHistory polarisation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
          UnaryHistory readback ∧ UnaryHistory metaplectic ∧ UnaryHistory endpoint ∧
            Cont symplectic line readback ∧ Cont readback polarisation metaplectic ∧
              Cont provenance metaplectic endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have lineUnary : UnaryHistory line := packet.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.left lineUnary packet.right.right.right.right.right.right.left
  have polarisationUnary : UnaryHistory polarisation := packet.right.right.right.left
  have metaplecticUnary : UnaryHistory metaplectic :=
    unary_cont_closed readbackUnary polarisationUnary
      packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary metaplecticUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, lineUnary, polarisationUnary,
      packet.right.right.right.right.left, provenanceUnary, readbackUnary, metaplecticUnary,
      endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.GeomQuantizationUp
