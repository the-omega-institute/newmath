import BEDC.Derived.FiniteCoverNerveUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteCoverNerveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCoverNerveCompactUniformHandoff [AskSetup] [PackageSetup]
    {cover nerve compact uniform transport replay provenance localName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory cover ->
      UnaryHistory nerve ->
        UnaryHistory compact ->
          UnaryHistory uniform ->
            UnaryHistory transport ->
              UnaryHistory replay ->
                UnaryHistory provenance ->
                  UnaryHistory localName ->
                    Cont cover nerve compact ->
                      Cont compact uniform transport ->
                        Cont transport replay handoffRead ->
                          PkgSig bundle provenance pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row cover ∨ hsame row nerve ∨
                                    hsame row compact ∨ hsame row uniform ∨
                                      hsame row transport ∨ hsame row replay ∨
                                        hsame row provenance ∨ hsame row localName ∨
                                          hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont cover nerve compact ∧
                                    Cont compact uniform transport ∧
                                      Cont transport replay handoffRead ∧
                                        PkgSig bundle provenance pkg)
                                hsame ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro coverUnary nerveUnary _compactUnary uniformUnary _transportUnary replayUnary
    _provenanceUnary _localNameUnary compactRoute transportRoute handoffRoute packageRead
  have compactUnary : UnaryHistory compact :=
    unary_cont_closed coverUnary nerveUnary compactRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed compactUnary uniformUnary transportRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed transportUnary replayUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row nerve ∨ hsame row compact ∨ hsame row uniform ∨
              hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover nerve compact ∧ Cont compact uniform transport ∧
              Cont transport replay handoffRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, transportRoute, handoffRoute, packageRead⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.FiniteCoverNerveUp
