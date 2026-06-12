import BEDC.Derived.RealUniformEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealUniformEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformEmbeddingSealHandoff [AskSetup] [PackageSetup]
    {S W D Q E U H C P N windowRead toleranceRead readbackRead uniformRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory Q →
            UnaryHistory E →
              UnaryHistory U →
                UnaryHistory P →
                  Cont S W windowRead →
                    Cont windowRead D toleranceRead →
                      Cont toleranceRead Q readbackRead →
                        Cont readbackRead U uniformRead →
                          Cont uniformRead E sealRead →
                            Cont sealRead P publicRead →
                              PkgSig bundle publicRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row S ∨ hsame row W ∨ hsame row D ∨
                                        hsame row Q ∨ hsame row E ∨ hsame row U ∨
                                          hsame row H ∨ hsame row C ∨ hsame row P ∨
                                            hsame row N ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont S W windowRead ∧
                                        Cont windowRead D toleranceRead ∧
                                          Cont toleranceRead Q readbackRead ∧
                                            Cont readbackRead U uniformRead ∧
                                              Cont uniformRead E sealRead ∧
                                                Cont sealRead P publicRead ∧
                                                  PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro sUnary wUnary dUnary qUnary eUnary uUnary pUnary windowRoute toleranceRoute
    readbackRoute uniformRoute sealRoute publicRoute publicPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary wUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary qUnary readbackRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed readbackUnary uUnary uniformRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed uniformUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨
              hsame row E ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W windowRead ∧ Cont windowRead D toleranceRead ∧
              Cont toleranceRead Q readbackRead ∧ Cont readbackRead U uniformRead ∧
                Cont uniformRead E sealRead ∧ Cont sealRead P publicRead ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, readbackRoute, uniformRoute, sealRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RealUniformEmbeddingUp
