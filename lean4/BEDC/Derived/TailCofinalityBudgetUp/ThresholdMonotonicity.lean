import BEDC.Derived.TailCofinalityBudgetUp.NameCertObligations
import BEDC.Derived.TailCofinalityBudgetUp.TasteGate
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

theorem TailCofinalityBudgetThresholdMonotonicity [AskSetup] [PackageSetup]
    {x : TailCofinalityBudgetUp}
    {R R' W D Q E H C P N refinedRead windowRead sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] →
      hsame R R' →
        UnaryHistory R' →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory N →
                    Cont R' W refinedRead →
                      Cont refinedRead D windowRead →
                        Cont windowRead Q sealRead →
                          Cont sealRead E consumer →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row consumer ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row consumer ∧ Cont R' W refinedRead ∧
                                      Cont refinedRead D windowRead ∧
                                        Cont windowRead Q sealRead ∧
                                          Cont sealRead E consumer)
                                  (fun row : BHist =>
                                    hsame row consumer ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory refinedRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fields thresholdSame unaryRefined unaryWindow unaryDyadic unaryReadback unarySeal
    unaryName refinedRoute windowRoute sealRoute consumerRoute namePkg
  have fieldWitness :
      tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] :=
    fields
  have thresholdWitness : hsame R R' := thresholdSame
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed unaryRefined unaryWindow refinedRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed refinedReadUnary unaryDyadic windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary unaryReadback sealRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealReadUnary unarySeal consumerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row consumer ∧ Cont R' W refinedRead ∧
            Cont refinedRead D windowRead ∧ Cont windowRead Q sealRead ∧
              Cont sealRead E consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact ⟨source.left, refinedRoute, windowRoute, sealRoute, consumerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  have _fieldWitnessUsed := fieldWitness
  have _thresholdWitnessUsed := thresholdWitness
  have _nameUnaryUsed := unaryName
  exact ⟨cert, refinedReadUnary, windowReadUnary, sealReadUnary, consumerUnary⟩

end BEDC.Derived.TailCofinalityBudgetUp
