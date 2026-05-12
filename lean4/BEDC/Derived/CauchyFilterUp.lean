import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream window threshold endpoint compatibility transport consumer provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧ UnaryHistory endpoint ∧
    UnaryHistory compatibility ∧ Cont stream window transport ∧
      Cont threshold endpoint compatibility ∧ Cont transport compatibility consumer ∧
        Cont consumer endpoint provenance ∧ PkgSig bundle provenance pkg

theorem CauchyFilterPacket_finite_window_coverage [AskSetup] [PackageSetup]
    {stream window threshold endpoint compatibility transport consumer provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream window threshold endpoint compatibility transport consumer provenance
        bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧ UnaryHistory endpoint ∧
        UnaryHistory compatibility ∧ UnaryHistory transport ∧ UnaryHistory consumer ∧
          UnaryHistory provenance ∧ hsame transport (append stream window) ∧
            hsame compatibility (append threshold endpoint) ∧
              hsame consumer (append transport compatibility) ∧
                hsame provenance (append consumer endpoint) ∧ PkgSig bundle provenance pkg := by
  intro packet
  have streamUnary : UnaryHistory stream :=
    packet.left
  have windowUnary : UnaryHistory window :=
    packet.right.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.left
  have compatibilityUnary : UnaryHistory compatibility :=
    packet.right.right.right.right.left
  have transportRow : Cont stream window transport :=
    packet.right.right.right.right.right.left
  have compatibilityRow : Cont threshold endpoint compatibility :=
    packet.right.right.right.right.right.right.left
  have consumerRow : Cont transport compatibility consumer :=
    packet.right.right.right.right.right.right.right.left
  have provenanceRow : Cont consumer endpoint provenance :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamUnary windowUnary transportRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed transportUnary compatibilityUnary consumerRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed consumerUnary endpointUnary provenanceRow
  exact And.intro streamUnary
    (And.intro windowUnary
      (And.intro thresholdUnary
        (And.intro endpointUnary
          (And.intro compatibilityUnary
            (And.intro transportUnary
              (And.intro consumerUnary
                (And.intro provenanceUnary
                  (And.intro transportRow
                    (And.intro compatibilityRow
                      (And.intro consumerRow
                        (And.intro provenanceRow pkgSig)))))))))))

end BEDC.Derived.CauchyFilterUp
