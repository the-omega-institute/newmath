import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StateSpaceModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StateSpaceModelPacket [AskSetup] [PackageSetup]
    (state input output transition inputMap observation trace controlRoute readback provenance
      hidden : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory output ∧
    UnaryHistory transition ∧ UnaryHistory inputMap ∧ UnaryHistory observation ∧
      UnaryHistory trace ∧ UnaryHistory controlRoute ∧ UnaryHistory readback ∧
        UnaryHistory provenance ∧ UnaryHistory hidden ∧ Cont state input transition ∧
          Cont transition inputMap trace ∧ Cont output observation readback ∧
            Cont trace readback provenance ∧ PkgSig bundle provenance pkg

theorem StateSpaceModelPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {state input output transition inputMap observation trace controlRoute readback provenance
      hidden : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
        readback provenance hidden bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance hidden bundle pkg ∧ hsame row hidden)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance hidden bundle pkg ∧ hsame row hidden)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance hidden bundle pkg ∧ hsame row hidden)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig NameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro hidden (And.intro packet (hsame_refl hidden))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.StateSpaceModelUp
