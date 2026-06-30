import BEDC.Derived.CompactMetricCompletionUp.Core

namespace BEDC.Derived.CompactMetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactMetricCompletionUniformModulusSeal [AskSetup] [PackageSetup]
    {T U B K E H C P N finiteNet completionSeal modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricCompletionCarrier T U B K E H C P N bundle pkg →
      Cont B T finiteNet →
        Cont U E completionSeal →
          Cont finiteNet completionSeal modulusRead →
            PkgSig bundle modulusRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row T ∨ hsame row U ∨ hsame row E ∨
                      hsame row K ∨ hsame row modulusRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B T finiteNet ∧ Cont U E completionSeal ∧
                      Cont finiteNet completionSeal modulusRead ∧
                        PkgSig bundle modulusRead pkg)
                  hsame ∧ UnaryHistory finiteNet ∧ UnaryHistory completionSeal ∧
                    UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier finiteRoute completionRoute modulusRoute modulusPkg
  have completionUnary : UnaryHistory T := carrier.left
  have uniformUnary : UnaryHistory U := carrier.right.left
  have ledgerUnary : UnaryHistory B := carrier.right.right.left
  have compactUnary : UnaryHistory K := carrier.right.right.right.left
  have realUnary : UnaryHistory E := carrier.right.right.right.right.left
  have finiteUnary : UnaryHistory finiteNet :=
    unary_cont_closed ledgerUnary completionUnary finiteRoute
  have completionSealUnary : UnaryHistory completionSeal :=
    unary_cont_closed uniformUnary realUnary completionRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed finiteUnary completionSealUnary modulusRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro modulusRead (And.intro (hsame_refl modulusRead) modulusUnary)
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
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro row source
        exact
          And.intro source.right
            (And.intro finiteRoute
              (And.intro completionRoute (And.intro modulusRoute modulusPkg)))
    }
  · exact And.intro finiteUnary (And.intro completionSealUnary modulusUnary)

end BEDC.Derived.CompactMetricCompletionUp
