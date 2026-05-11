import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptimalTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptimalTransportFiniteCouplingPacket [AskSetup] [PackageSetup]
    (source target sourceMass targetMass cost coupling marginal objective feasible dual
      certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory marginal ∧ UnaryHistory objective ∧ UnaryHistory feasible ∧
        UnaryHistory dual ∧ UnaryHistory certRow ∧
          Cont sourceMass targetMass marginal ∧ Cont cost coupling objective ∧
            Cont marginal objective feasible ∧ Cont feasible dual certRow ∧
              PkgSig bundle certRow pkg ∧ hsame source certRow ∧
                hsame target certRow ∧ hsame sourceMass certRow ∧
                  hsame targetMass certRow ∧ hsame cost certRow ∧
                    hsame coupling certRow ∧ hsame marginal certRow ∧
                      hsame objective certRow ∧ hsame feasible certRow ∧
                        hsame dual certRow

theorem OptimalTransportFiniteCouplingPacket_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {source target sourceMass targetMass cost coupling marginal objective feasible dual
      certRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket source target sourceMass targetMass cost coupling
        marginal objective feasible dual certRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row sourceMass ∨
              hsame row targetMass ∨ hsame row cost ∨ hsame row coupling ∨
                hsame row marginal ∨ hsame row objective ∨ hsame row feasible ∨
                  hsame row dual ∨ hsame row certRow)
          (fun row : BHist =>
            hsame row marginal ∨ hsame row objective ∨ hsame row feasible ∨
              hsame row dual ∨ hsame row certRow)
          (fun row : BHist => hsame row certRow)
          hsame ∧
        Cont sourceMass targetMass marginal ∧ Cont cost coupling objective ∧
          Cont marginal objective feasible ∧ Cont feasible dual certRow ∧
            PkgSig bundle certRow pkg := by
  intro packet
  obtain ⟨_sourceUnary, _targetUnary, _sourceMassUnary, _targetMassUnary, _costUnary,
    _couplingUnary, _marginalUnary, _objectiveUnary, _feasibleUnary, _dualUnary,
    _certUnary, sourceMassTargetMassMarginal, costCouplingObjective,
    marginalObjectiveFeasible, feasibleDualCert, packageCert, sourceCert, targetCert,
    sourceMassCert, targetMassCert, costCert, couplingCert, marginalCert, objectiveCert,
    feasibleCert, dualCert⟩ := packet
  have certRowSource :
      hsame certRow source ∨ hsame certRow target ∨ hsame certRow sourceMass ∨
        hsame certRow targetMass ∨ hsame certRow cost ∨ hsame certRow coupling ∨
          hsame certRow marginal ∨ hsame certRow objective ∨ hsame certRow feasible ∨
            hsame certRow dual ∨ hsame certRow certRow :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (hsame_refl certRow))))))))))
  have sourceToCert :
      forall {row : BHist},
        (hsame row source ∨ hsame row target ∨ hsame row sourceMass ∨
          hsame row targetMass ∨ hsame row cost ∨ hsame row coupling ∨
            hsame row marginal ∨ hsame row objective ∨ hsame row feasible ∨
              hsame row dual ∨ hsame row certRow) ->
          hsame row certRow := by
    intro row sourceVisible
    cases sourceVisible with
    | inl sameSource =>
        exact hsame_trans sameSource sourceCert
    | inr sourceVisible =>
        cases sourceVisible with
        | inl sameTarget =>
            exact hsame_trans sameTarget targetCert
        | inr sourceVisible =>
            cases sourceVisible with
            | inl sameSourceMass =>
                exact hsame_trans sameSourceMass sourceMassCert
            | inr sourceVisible =>
                cases sourceVisible with
                | inl sameTargetMass =>
                    exact hsame_trans sameTargetMass targetMassCert
                | inr sourceVisible =>
                    cases sourceVisible with
                    | inl sameCost =>
                        exact hsame_trans sameCost costCert
                    | inr sourceVisible =>
                        cases sourceVisible with
                        | inl sameCoupling =>
                            exact hsame_trans sameCoupling couplingCert
                        | inr sourceVisible =>
                            cases sourceVisible with
                            | inl sameMarginal =>
                                exact hsame_trans sameMarginal marginalCert
                            | inr sourceVisible =>
                                cases sourceVisible with
                                | inl sameObjective =>
                                    exact hsame_trans sameObjective objectiveCert
                                | inr sourceVisible =>
                                    cases sourceVisible with
                                    | inl sameFeasible =>
                                        exact hsame_trans sameFeasible feasibleCert
                                    | inr sourceVisible =>
                                        cases sourceVisible with
                                        | inl sameDual =>
                                            exact hsame_trans sameDual dualCert
                                        | inr sameCert =>
                                            exact sameCert
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row sourceMass ∨
              hsame row targetMass ∨ hsame row cost ∨ hsame row coupling ∨
                hsame row marginal ∨ hsame row objective ∨ hsame row feasible ∨
                  hsame row dual ∨ hsame row certRow)
          (fun row : BHist =>
            hsame row marginal ∨ hsame row objective ∨ hsame row feasible ∨
              hsame row dual ∨ hsame row certRow)
          (fun row : BHist => hsame row certRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro certRow certRowSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same sourceVisible
        cases sourceVisible with
        | inl sameSource =>
            exact Or.inl (hsame_trans (hsame_symm same) sameSource)
        | inr sourceVisible =>
            cases sourceVisible with
            | inl sameTarget =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameTarget))
            | inr sourceVisible =>
                cases sourceVisible with
                | inl sameSourceMass =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameSourceMass)))
                | inr sourceVisible =>
                    cases sourceVisible with
                    | inl sameTargetMass =>
                        exact Or.inr (Or.inr (Or.inr
                          (Or.inl (hsame_trans (hsame_symm same) sameTargetMass))))
                    | inr sourceVisible =>
                        cases sourceVisible with
                        | inl sameCost =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inl (hsame_trans (hsame_symm same) sameCost)))))
                        | inr sourceVisible =>
                            cases sourceVisible with
                            | inl sameCoupling =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm same) sameCoupling))))))
                            | inr sourceVisible =>
                                cases sourceVisible with
                                | inl sameMarginal =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm same) sameMarginal)))))))
                                | inr sourceVisible =>
                                    cases sourceVisible with
                                    | inl sameObjective =>
                                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                          (Or.inr (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm same)
                                                sameObjective))))))))
                                    | inr sourceVisible =>
                                        cases sourceVisible with
                                        | inl sameFeasible =>
                                            exact Or.inr (Or.inr (Or.inr (Or.inr
                                              (Or.inr (Or.inr (Or.inr (Or.inr
                                                (Or.inl
                                                  (hsame_trans (hsame_symm same)
                                                    sameFeasible)))))))))
                                        | inr sourceVisible =>
                                            cases sourceVisible with
                                            | inl sameDual =>
                                                exact Or.inr (Or.inr (Or.inr (Or.inr
                                                  (Or.inr (Or.inr (Or.inr (Or.inr
                                                    (Or.inr
                                                      (Or.inl
                                                        (hsame_trans (hsame_symm same)
                                                          sameDual))))))))))
                                            | inr sameCert =>
                                                exact Or.inr (Or.inr (Or.inr (Or.inr
                                                  (Or.inr (Or.inr (Or.inr (Or.inr
                                                    (Or.inr (Or.inr
                                                      (hsame_trans (hsame_symm same)
                                                        sameCert))))))))))
    }
    pattern_sound := by
      intro row sourceVisible
      exact Or.inr (Or.inr (Or.inr (Or.inr (sourceToCert sourceVisible))))
    ledger_sound := by
      intro row sourceVisible
      exact sourceToCert sourceVisible
  }
  exact
    ⟨cert, sourceMassTargetMassMarginal, costCouplingObjective,
      marginalObjectiveFeasible, feasibleDualCert, packageCert⟩

end BEDC.Derived.OptimalTransportUp
