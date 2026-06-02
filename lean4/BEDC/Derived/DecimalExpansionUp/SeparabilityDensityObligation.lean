import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionSeparabilityDensityObligation [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead dyadicRead regseqRead sealRead
      structuralRead densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont D W prefixRead →
                          Cont prefixRead V placeRead →
                            Cont placeRead Q dyadicRead →
                              Cont dyadicRead R regseqRead →
                                Cont regseqRead E sealRead →
                                  Cont sealRead C structuralRead →
                                    Cont structuralRead N densityRead →
                                      PkgSig bundle densityRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row densityRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row D ∨ hsame row W ∨ hsame row V ∨
                                                hsame row Q ∨ hsame row R ∨ hsame row E ∨
                                                  hsame row densityRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ PkgSig bundle densityRead pkg)
                                            hsame ∧
                                          UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro dUnary wUnary vUnary qUnary rUnary eUnary _hUnary cUnary _pUnary nUnary
  intro prefixRoute placeRoute dyadicRoute regseqRoute sealRoute structuralRoute
  intro densityRoute densityPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed placeUnary qUnary dyadicRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary rUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary eUnary sealRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed sealUnary cUnary structuralRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed structuralUnary nUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨
              hsame row R ∨ hsame row E ∨ hsame row densityRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, densityPkg⟩
  }
  exact ⟨cert, densityUnary⟩

end BEDC.Derived.DecimalExpansionUp
