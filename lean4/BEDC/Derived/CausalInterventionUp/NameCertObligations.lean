import BEDC.Derived.CausalInterventionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CausalInterventionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CausalInterventionCarrier [AskSetup] [PackageSetup]
    (M S T D J R K H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory D ∧
    UnaryHistory J ∧ UnaryHistory R ∧ UnaryHistory K ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem CausalInterventionNameCertObligations [AskSetup] [PackageSetup]
    {M S T D J R K H C P N dependencyRead interventionRead rateRead
      commitmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CausalInterventionCarrier M S T D J R K H C P N bundle pkg →
      Cont T D dependencyRead →
        Cont dependencyRead J interventionRead →
          Cont interventionRead R rateRead →
            Cont rateRead K commitmentRead →
              SemanticNameCert
                  (fun row : BHist => hsame row commitmentRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row S ∨ hsame row T ∨ hsame row D ∨
                      hsame row J ∨ hsame row R ∨ hsame row K ∨ hsame row commitmentRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont T D dependencyRead ∧
                      Cont dependencyRead J interventionRead ∧
                        Cont interventionRead R rateRead ∧ Cont rateRead K commitmentRead ∧
                          PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory dependencyRead ∧ UnaryHistory interventionRead ∧
                  UnaryHistory rateRead ∧ UnaryHistory commitmentRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier dependencyRoute interventionRoute rateRoute commitmentRoute
  obtain ⟨_mUnary, _sUnary, tUnary, dUnary, jUnary, rUnary, kUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed tUnary dUnary dependencyRoute
  have interventionUnary : UnaryHistory interventionRead :=
    unary_cont_closed dependencyUnary jUnary interventionRoute
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed interventionUnary rUnary rateRoute
  have commitmentUnary : UnaryHistory commitmentRead :=
    unary_cont_closed rateUnary kUnary commitmentRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row commitmentRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row T ∨ hsame row D ∨ hsame row J ∨
              hsame row R ∨ hsame row K ∨ hsame row commitmentRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T D dependencyRead ∧
              Cont dependencyRead J interventionRead ∧ Cont interventionRead R rateRead ∧
                Cont rateRead K commitmentRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro commitmentRead ⟨hsame_refl commitmentRead, commitmentUnary⟩
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
      exact
        ⟨source.right, dependencyRoute, interventionRoute, rateRoute, commitmentRoute,
          provenancePkg⟩
  }
  exact ⟨cert, dependencyUnary, interventionUnary, rateUnary, commitmentUnary⟩

end BEDC.Derived.CausalInterventionUp
