import BEDC.Derived.RegularCauchyTailEstimateUp.ModulusDominanceCriterion
import BEDC.Derived.RegularCauchyTailEstimateUp.RegSeqRatHandoff

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimatePublicInterface [AskSetup] [PackageSetup]
    {M W D R E H C P N toleranceRead windowRead readbackRead handoffRead dominanceRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      Cont D W toleranceRead →
        Cont toleranceRead R windowRead →
          Cont windowRead E readbackRead →
            Cont readbackRead C handoffRead →
              Cont M D dominanceRead →
                Cont handoffRead dominanceRead publicRead →
                  PkgSig bundle handoffRead pkg →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                              hsame row C ∨ hsame row handoffRead ∨
                                hsame row dominanceRead ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont D W toleranceRead ∧
                              Cont toleranceRead R windowRead ∧
                                Cont windowRead E readbackRead ∧
                                  Cont readbackRead C handoffRead ∧
                                    Cont M D dominanceRead ∧
                                      Cont handoffRead dominanceRead publicRead ∧
                                        PkgSig bundle handoffRead pkg ∧
                                          PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier toleranceRoute windowRoute readbackRoute handoffRoute dominanceRoute
    publicRoute handoffPkg publicPkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, unaryC, _unaryP, _unaryN,
    _carrierPkg, _carrierName⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryD unaryW toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary unaryR windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryE readbackRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed readbackUnary unaryC handoffRoute
  have dominanceUnary : UnaryHistory dominanceRead :=
    unary_cont_closed unaryM unaryD dominanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed handoffUnary dominanceUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row C ∨
              hsame row handoffRead ∨ hsame row dominanceRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W toleranceRead ∧
              Cont toleranceRead R windowRead ∧ Cont windowRead E readbackRead ∧
                Cont readbackRead C handoffRead ∧ Cont M D dominanceRead ∧
                  Cont handoffRead dominanceRead publicRead ∧ PkgSig bundle handoffRead pkg ∧
                    PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        ⟨source.right, toleranceRoute, windowRoute, readbackRoute, handoffRoute,
          dominanceRoute, publicRoute, handoffPkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
