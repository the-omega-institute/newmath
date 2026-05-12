import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyOscillationPacket [AskSetup] [PackageSetup]
    (tailWindow modulus tolerance oscillation sealRow transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory oscillation ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont tailWindow modulus tolerance ∧ Cont tolerance oscillation sealRow ∧
          Cont sealRow transport routes ∧ Cont routes provenance name ∧ PkgSig bundle name pkg

theorem CauchyOscillationPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance oscillation sealRow transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          CauchyOscillationPacket tailWindow modulus tolerance oscillation sealRow transport routes
              provenance name bundle pkg ∧
            hsame row name)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name (And.intro packet (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyOscillationUp
