import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionPrefixDensityExhaustion [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead toleranceRead readbackRead sealRead
      densityRead namedRead publicRead : BHist}
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
                            Cont placeRead Q toleranceRead →
                              Cont toleranceRead R readbackRead →
                                Cont readbackRead E sealRead →
                                  Cont sealRead H densityRead →
                                    Cont densityRead C namedRead →
                                      PkgSig bundle P pkg →
                                        PkgSig bundle N pkg →
                                          hsame publicRead densityRead →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row publicRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row D ∨ hsame row W ∨
                                                    hsame row V ∨ hsame row Q ∨
                                                      hsame row R ∨ hsame row E ∨
                                                        hsame row densityRead ∨
                                                          hsame row publicRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                                hsame ∧
                                              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary cUnary _pUnary _nUnary
    prefixRoute placeRoute toleranceRoute readbackRoute sealRoute densityRoute namedRoute
    provenancePkg namePkg samePublicDensity
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed sealUnary hUnary densityRoute
  have _namedUnary : UnaryHistory namedRead :=
    unary_cont_closed densityUnary cUnary namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_transport_symm densityUnary samePublicDensity
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row densityRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.DecimalExpansionUp
