import BEDC.Derived.TailCofinalityBudgetUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailCofinalityBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityBudgetFilteredTailScope [AskSetup] [PackageSetup]
    {x : TailCofinalityBudgetUp}
    {R W D Q E H C P N windowRead sealRead consumer refined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] →
      Cont R W D →
        Cont D Q windowRead →
          Cont windowRead E sealRead →
            Cont sealRead N consumer →
              Cont R consumer refined →
                UnaryHistory R →
                  UnaryHistory W →
                    UnaryHistory Q →
                      UnaryHistory E →
                        UnaryHistory N →
                          PkgSig bundle N pkg →
                            PkgSig bundle refined pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row refined ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row refined ∧ Cont R consumer refined ∧
                                      Cont R W D ∧ Cont D Q windowRead ∧
                                        Cont windowRead E sealRead ∧
                                          Cont sealRead N consumer)
                                  (fun row : BHist =>
                                    hsame row refined ∧ PkgSig bundle refined pkg)
                                  hsame ∧
                                UnaryHistory D ∧ UnaryHistory windowRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory consumer ∧
                                    UnaryHistory refined := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _fields routeD routeWindow routeSeal routeConsumer routeRefined unaryR unaryW unaryQ
    unaryE unaryN _namePkg refinedPkg
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryR unaryW routeD
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryD unaryQ routeWindow
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryWindow unaryE routeSeal
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unarySeal unaryN routeConsumer
  have unaryRefined : UnaryHistory refined :=
    unary_cont_closed unaryR unaryConsumer routeRefined
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refined ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row refined ∧ Cont R consumer refined ∧ Cont R W D ∧
            Cont D Q windowRead ∧ Cont windowRead E sealRead ∧ Cont sealRead N consumer)
        (fun row : BHist => hsame row refined ∧ PkgSig bundle refined pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refined ⟨hsame_refl refined, unaryRefined⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, routeRefined, routeD, routeWindow, routeSeal, routeConsumer⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refinedPkg⟩
  }
  exact ⟨cert, unaryD, unaryWindow, unarySeal, unaryConsumer, unaryRefined⟩

end BEDC.Derived.TailCofinalityBudgetUp
