import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LQRFiniteControlPacket [AskSetup] [PackageSetup]
    (state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧
    UnaryHistory control ∧
      UnaryHistory transition ∧
        UnaryHistory cost ∧
          UnaryHistory horizon ∧
            UnaryHistory successorValue ∧
              UnaryHistory estimatorInput ∧
                UnaryHistory backwardUpdate ∧
                  UnaryHistory predecessorValue ∧
                    UnaryHistory endpoint ∧
                      Cont state control transition ∧
                        Cont transition cost successorValue ∧
                          Cont successorValue estimatorInput backwardUpdate ∧
                            Cont backwardUpdate horizon predecessorValue ∧
                              Cont predecessorValue cost endpoint ∧ PkgSig bundle endpoint pkg

theorem LQRFiniteControlPacket_namecert_seed_obligation_surface [AskSetup] [PackageSetup]
    {state control transition cost horizon successorValue estimatorInput backwardUpdate
      predecessorValue endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon successorValue estimatorInput
      backwardUpdate predecessorValue endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              LQRFiniteControlPacket state control transition cost horizon successorValue
                estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont successorValue estimatorInput backwardUpdate ∧
          Cont backwardUpdate horizon predecessorValue ∧ PkgSig bundle endpoint pkg := by
  intro packet
  let Carrier : BHist -> Prop :=
    fun row : BHist =>
      exists e : BHist,
        LQRFiniteControlPacket state control transition cost horizon successorValue
          estimatorInput backwardUpdate predecessorValue e bundle pkg ∧ hsame row e
  have endpointCarrier : Carrier endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointCarrier
      equiv_refl := by
        intro row _rowCarrier
        exact hsame_refl row
      equiv_symm := by
        intro row other rowOther
        exact hsame_symm rowOther
      equiv_trans := by
        intro row middle other rowMiddle middleOther
        exact hsame_trans rowMiddle middleOther
      carrier_respects_equiv := by
        intro row other rowOther rowCarrier
        cases rowCarrier with
        | intro e rowWitness =>
            exact Exists.intro e
              (And.intro rowWitness.left (hsame_trans (hsame_symm rowOther) rowWitness.right))
    }
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  have backwardCont : Cont successorValue estimatorInput backwardUpdate :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have predecessorCont : Cont backwardUpdate horizon predecessorValue :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgRow : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro cert (And.intro backwardCont (And.intro predecessorCont pkgRow))

end BEDC.Derived.LQRUp
