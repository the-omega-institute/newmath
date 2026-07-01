import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularSequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularSequenceSpacePacket [AskSetup] [PackageSetup]
    (X T Q D R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory T ∧ UnaryHistory Q ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont X T Q ∧ Cont Q D R ∧ Cont R H C ∧ PkgSig bundle P pkg

theorem RegularSequenceSpaceNameCertObligations [AskSetup] [PackageSetup]
    {X T Q D R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularSequenceSpacePacket X T Q D R H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            RegularSequenceSpacePacket X T Q D R H C P N bundle pkg ∧ hsame row R)
          (fun row : BHist =>
            RegularSequenceSpacePacket X T Q D R H C P N bundle pkg ∧ hsame row R)
          (fun row : BHist =>
            RegularSequenceSpacePacket X T Q D R H C P N bundle pkg ∧ hsame row R)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory T ∧ UnaryHistory Q ∧ UnaryHistory D ∧
          UnaryHistory R ∧ PkgSig bundle P pkg := by
  intro packet
  let Surface : BHist -> Prop :=
    fun row : BHist =>
      RegularSequenceSpacePacket X T Q D R H C P N bundle pkg ∧ hsame row R
  have sealSource : Surface R :=
    And.intro packet (hsame_refl R)
  have cert : SemanticNameCert Surface Surface Surface hsame := {
    core := {
      carrier_inhabited := Exists.intro R sealSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, packet.left, packet.right.left, packet.right.right.left,
      packet.right.right.right.left, packet.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RegularSequenceSpaceUp
