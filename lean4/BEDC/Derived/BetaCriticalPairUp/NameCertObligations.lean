import BEDC.Derived.BetaCriticalPairUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BetaCriticalPairUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BetaCriticalPairNameCertObligations [AskSetup] [PackageSetup]
    {O L R J B H C P N leftRead rightRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory O ->
      UnaryHistory L ->
        UnaryHistory R ->
          UnaryHistory B ->
            Cont O L leftRead ->
              Cont O R rightRead ->
                Cont leftRead rightRead J ->
                  Cont J B boundaryRead ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          Cont O L leftRead ∧ Cont O R rightRead ∧
                            Cont leftRead rightRead J ∧ Cont J B row)
                        (fun row : BHist => hsame row boundaryRead ∧ PkgSig bundle N pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryO unaryL unaryR unaryB leftRoute rightRoute joinRoute boundaryRoute namePkg
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed unaryO unaryL leftRoute
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed unaryO unaryR rightRoute
  have joinUnary : UnaryHistory J :=
    unary_cont_closed leftReadUnary rightReadUnary joinRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed joinUnary unaryB boundaryRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
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
      exact ⟨leftRoute, rightRoute, joinRoute,
        cont_result_hsame_transport boundaryRoute (hsame_symm source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }

end BEDC.Derived.BetaCriticalPairUp
