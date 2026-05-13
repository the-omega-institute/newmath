import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FibonacciInverseLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FibonacciInverseLimitPacket [AskSetup] [PackageSetup]
    (golden cube window projection transport routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory golden ∧ UnaryHistory cube ∧ UnaryHistory window ∧ UnaryHistory projection ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
      Cont golden cube window ∧ Cont window projection routes ∧
        Cont routes transport provenance ∧ PkgSig bundle provenance pkg

theorem FibonacciInverseLimitPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {golden cube window projection transport routes provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FibonacciInverseLimitPacket golden cube window projection transport routes provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FibonacciInverseLimitPacket golden cube window projection transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FibonacciInverseLimitPacket golden cube window projection transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FibonacciInverseLimitPacket golden cube window projection transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        hsame ∧
        UnaryHistory golden ∧ UnaryHistory cube ∧ UnaryHistory window ∧
          UnaryHistory projection ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
            Cont golden cube window ∧ Cont window projection routes ∧
              Cont routes transport provenance ∧ PkgSig bundle provenance pkg := by
  intro packet
  let Carrier : BHist → Prop :=
    fun row =>
      FibonacciInverseLimitPacket golden cube window projection transport routes provenance
        nameRow bundle pkg ∧ hsame row provenance
  have packetWitness :
      FibonacciInverseLimitPacket golden cube window projection transport routes provenance
        nameRow bundle pkg :=
    packet
  obtain ⟨goldenUnary, cubeUnary, windowUnary, projectionUnary, _transportUnary,
    provenanceUnary, nameRowUnary, goldenCubeWindow, windowProjectionRoutes,
    routesTransportProvenance, provenancePkg⟩ := packet
  have core : NameCert Carrier hsame := {
    carrier_inhabited :=
      Exists.intro provenance (And.intro packetWitness (hsame_refl provenance))
    equiv_refl := by
      intro row _rowCarrier
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' same
      exact hsame_symm same
    equiv_trans := by
      intro _row _row' _row'' same same'
      exact hsame_trans same same'
    carrier_respects_equiv := by
      intro _row _row' same rowCarrier
      exact And.intro rowCarrier.left (hsame_trans (hsame_symm same) rowCarrier.right)
  }
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, goldenUnary, cubeUnary, windowUnary, projectionUnary, provenanceUnary,
      nameRowUnary, goldenCubeWindow, windowProjectionRoutes, routesTransportProvenance,
      provenancePkg⟩

end BEDC.Derived.FibonacciInverseLimitUp
