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

theorem LayeredRelationGate_ledger_obligation [AskSetup] [PackageSetup]
    {A B L P N F G H C Pi sourceRead layerRead refusalRead verdictRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory B →
        UnaryHistory L →
          UnaryHistory F →
            UnaryHistory G →
              UnaryHistory Pi →
                Cont A B sourceRead →
                  Cont sourceRead L layerRead →
                    Cont layerRead F refusalRead →
                      Cont refusalRead G verdictRead →
                        Cont verdictRead Pi consumerRead →
                          PkgSig bundle Pi pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row F ∨ hsame row N ∨ hsame row G ∨
                                    hsame row consumerRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont layerRead F refusalRead ∧
                                    Cont refusalRead G verdictRead ∧
                                      Cont verdictRead Pi consumerRead ∧
                                        PkgSig bundle Pi pkg)
                                hsame ∧
                              UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary bUnary lUnary fUnary gUnary piUnary sourceRoute layerRoute refusalRoute
    verdictRoute consumerRoute provenancePkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed aUnary bUnary sourceRoute
  have layerUnary : UnaryHistory layerRead :=
    unary_cont_closed sourceUnary lUnary layerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed layerUnary fUnary refusalRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed refusalUnary gUnary verdictRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed verdictUnary piUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row F ∨ hsame row N ∨ hsame row G ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont layerRead F refusalRead ∧
              Cont refusalRead G verdictRead ∧ Cont verdictRead Pi consumerRead ∧
                PkgSig bundle Pi pkg)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, verdictRoute, consumerRoute, provenancePkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.LayeredRelationGateUp
