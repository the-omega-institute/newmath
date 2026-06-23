import BEDC.Derived.BinaryEndpointNormalizationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinaryEndpointNormalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinaryEndpointNormalization_dual_prefix_boundary [AskSetup] [PackageSetup]
    {L R K D A W Q S H C P N leftRead rightRead carryRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory K →
          UnaryHistory D →
            UnaryHistory A →
              UnaryHistory W →
                UnaryHistory Q →
                  Cont W L leftRead →
                    Cont W R rightRead →
                      Cont leftRead rightRead carryRead →
                        Cont carryRead Q handoffRead →
                          PkgSig bundle handoffRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row carryRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row L ∨ hsame row R ∨ hsame row K ∨
                                    hsame row D ∨ hsame row A ∨ hsame row W ∨
                                      hsame row carryRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W L leftRead ∧
                                    Cont W R rightRead ∧
                                      Cont leftRead rightRead carryRead ∧
                                        Cont carryRead Q handoffRead ∧
                                          PkgSig bundle handoffRead pkg)
                                hsame ∧
                              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                                UnaryHistory carryRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro lUnary rUnary _kUnary _dUnary _aUnary wUnary qUnary leftRoute rightRoute
    carryRoute handoffRoute handoffPkg
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed wUnary lUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed wUnary rUnary rightRoute
  have carryUnary : UnaryHistory carryRead :=
    unary_cont_closed leftUnary rightUnary carryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed carryUnary qUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row carryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row K ∨ hsame row D ∨ hsame row A ∨
              hsame row W ∨ hsame row carryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W L leftRead ∧ Cont W R rightRead ∧
              Cont leftRead rightRead carryRead ∧ Cont carryRead Q handoffRead ∧
                PkgSig bundle handoffRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro carryRead ⟨hsame_refl carryRead, carryUnary⟩
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
        exact ⟨source.right, leftRoute, rightRoute, carryRoute, handoffRoute, handoffPkg⟩
    }
  exact ⟨cert, leftUnary, rightUnary, carryUnary, handoffUnary⟩

end BEDC.Derived.BinaryEndpointNormalizationUp
