import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessFormalTargetLedger [AskSetup] [PackageSetup]
    {T S B F R _H C P N boundedFinished normalRead refusalRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory B →
          UnaryHistory F →
            UnaryHistory R →
              UnaryHistory C →
                Cont T S boundedFinished →
                  Cont B F normalRead →
                    Cont normalRead R refusalRead →
                      Cont refusalRead C targetRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row boundedFinished ∨ hsame row normalRead ∨
                                      hsame row refusalRead ∨ hsame row targetRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row S ∨ hsame row B ∨
                                    hsame row F ∨ hsame row R ∨ hsame row C ∨
                                      hsame row boundedFinished ∨ hsame row normalRead ∨
                                        hsame row refusalRead ∨ hsame row targetRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont T S boundedFinished ∧
                                    Cont B F normalRead ∧ Cont normalRead R refusalRead ∧
                                      Cont refusalRead C targetRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro typingUnary sameUnary boundedUnary finishedUnary refusalUnary continuationUnary
    typingSame boundedFinishedRoute normalRefusal refusalContinuation provenancePkg namePkg
  have boundedFinishedUnary : UnaryHistory boundedFinished :=
    unary_cont_closed typingUnary sameUnary typingSame
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed boundedUnary finishedUnary boundedFinishedRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed normalReadUnary refusalUnary normalRefusal
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed refusalReadUnary continuationUnary refusalContinuation
  have targetSource :
      (fun row : BHist =>
        (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row refusalRead ∨
            hsame row targetRead) ∧
          UnaryHistory row) targetRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (hsame_refl targetRead))), targetReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row refusalRead ∨
                hsame row targetRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
              hsame row C ∨ hsame row boundedFinished ∨ hsame row normalRead ∨
                hsame row refusalRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S boundedFinished ∧ Cont B F normalRead ∧
              Cont normalRead R refusalRead ∧ Cont refusalRead C targetRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead targetSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameBoundedFinished =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameBoundedFinished)
          | inr rest =>
              cases rest with
              | inl sameNormal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal))
              | inr restTail =>
                  cases restTail with
                  | inl sameRefusal =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameRefusal)))
                  | inr sameTarget =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameTarget)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBoundedFinished =>
          right
          right
          right
          right
          right
          right
          left
          exact sameBoundedFinished
      | inr rest =>
          cases rest with
          | inl sameNormal =>
              right
              right
              right
              right
              right
              right
              right
              left
              exact sameNormal
          | inr restTail =>
              cases restTail with
              | inl sameRefusal =>
                  right
                  right
                  right
                  right
                  right
                  right
                  right
                  right
                  left
                  exact sameRefusal
              | inr sameTarget =>
                  right
                  right
                  right
                  right
                  right
                  right
                  right
                  right
                  right
                  exact sameTarget
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, typingSame, boundedFinishedRoute, normalRefusal,
          refusalContinuation, provenancePkg, namePkg⟩
  }
  exact ⟨cert, targetReadUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
