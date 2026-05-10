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

theorem InfCatBHistSourcePacket_quasicategory_classifier_surface [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport simplicial' category' horn' lift'
      provenance' transport' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      hsame simplicial simplicial' -> hsame category category' -> hsame horn horn' ->
        hsame provenance provenance' -> Cont simplicial' horn' lift' ->
          Cont provenance' lift' transport' -> PkgSig bundle transport' pkg ->
            InfCatBHistSourcePacket simplicial' category' horn' lift' provenance' transport'
                bundle pkg ∧
              hsame lift lift' ∧ hsame transport transport' := by
  intro packet sameSimplicial sameCategory sameHorn sameProvenance liftRow' transportRow'
    pkgRow'
  have liftSame : hsame lift lift' :=
    cont_respects_hsame sameSimplicial sameHorn packet.right.right.right.right.right.left
      liftRow'
  have transportSame : hsame transport transport' :=
    cont_respects_hsame sameProvenance liftSame packet.right.right.right.right.right.right.left
      transportRow'
  have targetPacket :
      InfCatBHistSourcePacket simplicial' category' horn' lift' provenance' transport'
        bundle pkg := by
    exact ⟨unary_transport packet.left sameSimplicial,
      unary_transport packet.right.left sameCategory,
      unary_transport packet.right.right.left sameHorn,
      unary_transport packet.right.right.right.left liftSame,
      unary_transport packet.right.right.right.right.left sameProvenance,
      liftRow',
      transportRow',
      pkgRow'⟩
  exact And.intro targetPacket (And.intro liftSame transportSame)

end BEDC.Derived.InfCatUp
