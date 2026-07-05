import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BoundedRiemannConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive BoundedRiemannConvergenceUp : Type where
  | mk
      (darbouxPartition regulatedFamily approachWindow taggedSum darbouxBracket uniformBound
        realEquality componentTransport replay provenance localName : BHist) :
      BoundedRiemannConvergenceUp
  deriving DecidableEq

def boundedRiemannConvergenceRows : BoundedRiemannConvergenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRiemannConvergenceUp.mk darbouX regulatedFamily approachWindow taggedSum
      darbouxBracket uniformBound realEquality componentTransport replay provenance localName =>
      [darbouX, regulatedFamily, approachWindow, taggedSum, darbouxBracket, uniformBound,
        realEquality, componentTransport, replay, provenance, localName]

theorem BoundedRiemannConvergenceCarrier_darboux_handoff
    (D F A T S B E H C P N : BHist) :
    boundedRiemannConvergenceRows (BoundedRiemannConvergenceUp.mk D F A T S B E H C P N) =
        [D, F, A, T, S, B, E, H, C, P, N] ∧
      hsame D D ∧ hsame F F ∧
        Cont F A (append F A) ∧ Cont T S (append T S) ∧
          Cont S B (append S B) ∧ Cont B E (append B E) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  constructor
  · rfl
  · constructor
    · exact hsame_refl D
    · constructor
      · exact hsame_refl F
      · constructor
        · exact cont_intro rfl
        · constructor
          · exact cont_intro rfl
          · constructor
            · exact cont_intro rfl
            · exact cont_intro rfl

theorem BoundedRiemannConvergenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D F A T S B E H C P N familyRead bracketRead boundRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    boundedRiemannConvergenceRows (BoundedRiemannConvergenceUp.mk D F A T S B E H C P N) =
        [D, F, A, T, S, B, E, H, C, P, N] ->
      UnaryHistory D -> UnaryHistory F -> UnaryHistory A -> UnaryHistory T ->
        UnaryHistory S -> UnaryHistory B -> UnaryHistory E ->
          Cont F A familyRead -> Cont T S bracketRead ->
            Cont bracketRead B boundRead -> Cont boundRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row F ∨ hsame row A ∨ hsame row T ∨
                        hsame row S ∨ hsame row B ∨ hsame row E ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F A familyRead ∧ Cont T S bracketRead ∧
                        Cont bracketRead B boundRead ∧ Cont boundRead E sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory familyRead ∧ UnaryHistory bracketRead ∧
                    UnaryHistory boundRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame Cont SemanticNameCert
  intro rowsExact unaryD unaryF unaryA unaryT unaryS unaryB unaryE
  intro familyCont bracketCont boundCont sealCont pkgSig
  have rowProjection :
      boundedRiemannConvergenceRows (BoundedRiemannConvergenceUp.mk D F A T S B E H C P N) =
        [D, F, A, T, S, B, E, H, C, P, N] := rowsExact
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed unaryF unaryA familyCont
  have bracketUnary : UnaryHistory bracketRead :=
    unary_cont_closed unaryT unaryS bracketCont
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed bracketUnary unaryB boundCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed boundUnary unaryE sealCont
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row F ∨ hsame row A ∨ hsame row T ∨
              hsame row S ∨ hsame row B ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F A familyRead ∧ Cont T S bracketRead ∧
              Cont bracketRead B boundRead ∧ Cont boundRead E sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, familyCont, bracketCont, boundCont, sealCont, pkgSig⟩
  }
  cases rowProjection
  exact ⟨cert, familyUnary, bracketUnary, boundUnary, sealUnary⟩

end BEDC.Derived.BoundedRiemannConvergenceUp
