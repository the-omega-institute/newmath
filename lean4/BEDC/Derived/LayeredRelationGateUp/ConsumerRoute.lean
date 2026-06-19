import BEDC.Derived.LayeredRelationGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LayeredRelationGateConsumerRoute [AskSetup] [PackageSetup]
    {A B L P N F G H C Pi sourceRead layerRead verdictRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory B →
        UnaryHistory L →
          UnaryHistory P →
            UnaryHistory N →
              UnaryHistory F →
                UnaryHistory G →
                  UnaryHistory Pi →
                    Cont A B sourceRead →
                      Cont sourceRead L layerRead →
                        Cont P N verdictRead →
                          Cont verdictRead G consumerRead →
                            PkgSig bundle Pi pkg →
                              PkgSig bundle consumerRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row consumerRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row A ∨ hsame row B ∨ hsame row L ∨
                                        hsame row P ∨ hsame row N ∨ hsame row F ∨
                                          hsame row G ∨ hsame row H ∨ hsame row C ∨
                                            hsame row Pi ∨ hsame row consumerRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont A B sourceRead ∧
                                        Cont sourceRead L layerRead ∧
                                          Cont P N verdictRead ∧
                                            Cont verdictRead G consumerRead ∧
                                              PkgSig bundle Pi pkg ∧
                                                PkgSig bundle consumerRead pkg)
                                    hsame ∧
                                  UnaryHistory sourceRead ∧ UnaryHistory layerRead ∧
                                    UnaryHistory verdictRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary bUnary lUnary pUnary nUnary _fUnary gUnary _piUnary sourceRoute
    layerRoute verdictRoute consumerRoute provenancePkg consumerPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed aUnary bUnary sourceRoute
  have layerUnary : UnaryHistory layerRead :=
    unary_cont_closed sourceUnary lUnary layerRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed pUnary nUnary verdictRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed verdictUnary gUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row L ∨ hsame row P ∨ hsame row N ∨
              hsame row F ∨ hsame row G ∨ hsame row H ∨ hsame row C ∨
                hsame row Pi ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A B sourceRead ∧ Cont sourceRead L layerRead ∧
              Cont P N verdictRead ∧ Cont verdictRead G consumerRead ∧
                PkgSig bundle Pi pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, layerRoute, verdictRoute, consumerRoute,
          provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, sourceUnary, layerUnary, verdictUnary, consumerUnary⟩

end BEDC.Derived.LayeredRelationGateUp
