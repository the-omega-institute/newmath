import BEDC.Derived.LQRUp

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LQRFiniteControlPacket_public_namecert_export [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint publicRowHist : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
        backwardUpdate predecessorValue endpoint bundle pkg ->
      Cont endpoint backwardUpdate publicRowHist ->
        PkgSig bundle publicRowHist pkg ->
          SemanticNameCert (fun row : BHist => hsame row publicRowHist)
              (fun row : BHist => hsame row publicRowHist)
              (fun row : BHist => hsame row publicRowHist) hsame ∧
            UnaryHistory publicRowHist ∧ hsame publicRowHist (append endpoint backwardUpdate) ∧
              PkgSig bundle publicRowHist pkg := by
  intro packet publicRow publicSig
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have backwardUnary : UnaryHistory backwardUpdate :=
    packet.right.right.right.right.right.right.right.left
  have publicUnary : UnaryHistory publicRowHist :=
    unary_cont_closed endpointUnary backwardUnary publicRow
  have cert :
      SemanticNameCert (fun row : BHist => hsame row publicRowHist)
          (fun row : BHist => hsame row publicRowHist)
          (fun row : BHist => hsame row publicRowHist) hsame :=
    {
      core := {
        carrier_inhabited := Exists.intro publicRowHist (hsame_refl publicRowHist)
        equiv_refl := by
          intro row _rowPublic
          exact hsame_refl row
        equiv_symm := by
          intro row other rowOther
          exact hsame_symm rowOther
        equiv_trans := by
          intro row middle other rowMiddle middleOther
          exact hsame_trans rowMiddle middleOther
        carrier_respects_equiv := by
          intro row other rowOther rowPublic
          exact hsame_trans (hsame_symm rowOther) rowPublic
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact And.intro cert (And.intro publicUnary (And.intro publicRow publicSig))

end BEDC.Derived.LQRUp
