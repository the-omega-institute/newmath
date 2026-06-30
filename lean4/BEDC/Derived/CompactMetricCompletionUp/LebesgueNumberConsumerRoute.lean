import BEDC.Derived.CompactMetricCompletionUp.Core

namespace BEDC.Derived.CompactMetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactMetricCompletionLebesgueNumberConsumerRoute [AskSetup] [PackageSetup]
    {T U B K E H C P N finiteNet completionRead realRead coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricCompletionCarrier T U B K E H C P N bundle pkg →
      Cont B T finiteNet →
        Cont finiteNet U completionRead →
          Cont completionRead E realRead →
            Cont realRead K coverRead →
              PkgSig bundle coverRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row T ∨ hsame row U ∨ hsame row E ∨
                        hsame row K ∨ hsame row coverRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B T finiteNet ∧
                        Cont finiteNet U completionRead ∧ Cont completionRead E realRead ∧
                          Cont realRead K coverRead ∧ PkgSig bundle coverRead pkg)
                    hsame ∧
                  UnaryHistory finiteNet ∧ UnaryHistory completionRead ∧
                    UnaryHistory realRead ∧ UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier finiteRoute completionRoute realRoute coverRoute coverPkg
  have completionUnary : UnaryHistory T := carrier.left
  have uniformUnary : UnaryHistory U := carrier.right.left
  have ledgerUnary : UnaryHistory B := carrier.right.right.left
  have compactUnary : UnaryHistory K := carrier.right.right.right.left
  have realUnary : UnaryHistory E := carrier.right.right.right.right.left
  have finiteUnary : UnaryHistory finiteNet :=
    unary_cont_closed ledgerUnary completionUnary finiteRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary uniformUnary completionRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed completionReadUnary realUnary realRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed realReadUnary compactUnary coverRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro coverRead (And.intro (hsame_refl coverRead) coverReadUnary)
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
            And.intro (hsame_trans (hsame_symm sameRows) source.left)
              (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          And.intro source.right
            (And.intro finiteRoute
              (And.intro completionRoute (And.intro realRoute (And.intro coverRoute coverPkg))))
    }
  · exact And.intro finiteUnary
      (And.intro completionReadUnary (And.intro realReadUnary coverReadUnary))

end BEDC.Derived.CompactMetricCompletionUp
