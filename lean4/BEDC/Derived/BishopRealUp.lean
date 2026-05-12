import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealPacket [AskSetup] [PackageSetup]
    (schedule regseq endpoint modulus located apartness realSeal transportRow route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory regseq ∧ UnaryHistory endpoint ∧
    UnaryHistory modulus ∧ UnaryHistory located ∧ UnaryHistory apartness ∧
      UnaryHistory realSeal ∧ UnaryHistory transportRow ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont schedule regseq endpoint ∧
          Cont endpoint modulus realSeal ∧ Cont located apartness realSeal ∧
            PkgSig bundle provenance pkg

theorem BishopRealPacket_visible_route_readback [AskSetup] [PackageSetup]
    {schedule regseq endpoint modulus located apartness realSeal transportRow route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealPacket schedule regseq endpoint modulus located apartness realSeal transportRow route
        provenance nameCert bundle pkg ->
      UnaryHistory endpoint ∧ UnaryHistory realSeal ∧
        hsame endpoint (append schedule regseq) ∧ hsame realSeal (append endpoint modulus) ∧
          hsame realSeal (append located apartness) ∧ PkgSig bundle provenance pkg := by
  intro packet
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.left
  have sealUnary : UnaryHistory realSeal :=
    packet.right.right.right.right.right.right.left
  have endpointRoute : hsame endpoint (append schedule regseq) :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have sealModulusRoute : hsame realSeal (append endpoint modulus) :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sealLocatedRoute : hsame realSeal (append located apartness) :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨endpointUnary, sealUnary, endpointRoute, sealModulusRoute, sealLocatedRoute,
      provenancePkg⟩

end BEDC.Derived.BishopRealUp
