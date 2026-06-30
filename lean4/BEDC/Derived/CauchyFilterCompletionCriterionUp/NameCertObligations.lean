import BEDC.Derived.CauchyFilterCompletionCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionCriterionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q B F U S D R E H C P N basisRead completionRead windowRead toleranceRead
      readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory F ∧ UnaryHistory B ∧ UnaryHistory Q ∧ UnaryHistory S ∧
      UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E) →
      Cont F B basisRead →
        Cont basisRead Q completionRead →
          Cont completionRead S windowRead →
            Cont windowRead D toleranceRead →
              Cont toleranceRead R readbackRead →
                Cont readbackRead E sealRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row F ∨ hsame row B ∨ hsame row Q ∨
                              hsame row S ∨ hsame row D ∨ hsame row R ∨
                                hsame row E ∨ hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows basisRoute completionRoute windowRoute toleranceRoute readbackRoute sealRoute
    provenancePkg namePkg
  obtain ⟨fUnary, bUnary, qUnary, sUnary, dUnary, rUnary, eUnary⟩ := rows
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed fUnary bUnary basisRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed basisUnary qUnary completionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary sUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row Q ∨ hsame row S ∨
              hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CauchyFilterCompletionCriterionUp
