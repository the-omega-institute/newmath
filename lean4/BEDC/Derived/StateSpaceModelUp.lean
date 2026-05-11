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
      observed route hidden : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory output ∧
    UnaryHistory transition ∧ UnaryHistory inputMap ∧ UnaryHistory observation ∧
      UnaryHistory trace ∧ UnaryHistory controlRoute ∧ UnaryHistory readback ∧
        UnaryHistory provenance ∧ UnaryHistory observed ∧ UnaryHistory route ∧
          UnaryHistory hidden ∧ Cont state input transition ∧
            Cont transition inputMap trace ∧ Cont output observation readback ∧
              Cont trace readback provenance ∧ Cont trace observation observed ∧
                Cont observed hidden route ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle route pkg

theorem StateSpaceModelPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {state input output transition inputMap observation trace controlRoute readback provenance
      observed route hidden : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
        readback provenance observed route hidden bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance observed route hidden bundle pkg ∧ hsame row hidden)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance observed route hidden bundle pkg ∧ hsame row hidden)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace
            controlRoute readback provenance observed route hidden bundle pkg ∧ hsame row hidden)
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

theorem StateSpaceModelPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state input output transition inputMap observation trace controlRoute readback provenance
      observed route hidden : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
        readback provenance observed route hidden bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
              readback provenance observed route hidden bundle pkg ∧ hsame row route)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
              readback provenance observed route hidden bundle pkg ∧ hsame row route)
        (fun row : BHist =>
          StateSpaceModelPacket state input output transition inputMap observation trace controlRoute
              readback provenance observed route hidden bundle pkg ∧ hsame row route)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro route ⟨packet, hsame_refl route⟩
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
        intro row row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.StateSpaceModelUp
