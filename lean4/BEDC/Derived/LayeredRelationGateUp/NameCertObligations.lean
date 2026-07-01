import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

theorem LayeredRelationGateNameCertObligations [AskSetup] [PackageSetup]
    {A B L P N F G H C Pi sourceRead layerRead refusalRead verdictRead carrierRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory B →
        UnaryHistory L →
          UnaryHistory P →
            UnaryHistory N →
              UnaryHistory F →
                UnaryHistory G →
                  UnaryHistory C →
                    UnaryHistory Pi →
                      Cont A B sourceRead →
                        Cont sourceRead L layerRead →
                          Cont P N refusalRead →
                            Cont refusalRead F verdictRead →
                              Cont verdictRead G carrierRead →
                                Cont carrierRead C replayRead →
                                  PkgSig bundle Pi pkg →
                                    PkgSig bundle replayRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row replayRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row A ∨ hsame row B ∨ hsame row L ∨
                                              hsame row P ∨ hsame row N ∨ hsame row F ∨
                                                hsame row G ∨ hsame row H ∨ hsame row C ∨
                                                  hsame row Pi ∨ hsame row replayRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont A B sourceRead ∧
                                              Cont sourceRead L layerRead ∧
                                                Cont P N refusalRead ∧
                                                  Cont refusalRead F verdictRead ∧
                                                    Cont verdictRead G carrierRead ∧
                                                      Cont carrierRead C replayRead ∧
                                                        PkgSig bundle Pi pkg ∧
                                                          PkgSig bundle replayRead pkg)
                                          hsame ∧
                                        UnaryHistory sourceRead ∧ UnaryHistory layerRead ∧
                                          UnaryHistory refusalRead ∧ UnaryHistory verdictRead ∧
                                            UnaryHistory carrierRead ∧
                                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary bUnary lUnary pUnary nUnary fUnary gUnary cUnary _piUnary sourceRoute
    layerRoute refusalRoute verdictRoute carrierRoute replayRoute piPkg replayPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed aUnary bUnary sourceRoute
  have layerUnary : UnaryHistory layerRead :=
    unary_cont_closed sourceUnary lUnary layerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed pUnary nUnary refusalRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed refusalUnary fUnary verdictRoute
  have carrierUnary : UnaryHistory carrierRead :=
    unary_cont_closed verdictUnary gUnary carrierRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed carrierUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row L ∨ hsame row P ∨ hsame row N ∨
              hsame row F ∨ hsame row G ∨ hsame row H ∨ hsame row C ∨ hsame row Pi ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A B sourceRead ∧ Cont sourceRead L layerRead ∧
              Cont P N refusalRead ∧ Cont refusalRead F verdictRead ∧
                Cont verdictRead G carrierRead ∧ Cont carrierRead C replayRead ∧
                  PkgSig bundle Pi pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, layerRoute, refusalRoute, verdictRoute, carrierRoute,
          replayRoute, piPkg, replayPkg⟩
  }
  exact
    ⟨cert, sourceUnary, layerUnary, refusalUnary, verdictUnary, carrierUnary, replayUnary⟩

end BEDC.Derived.LayeredRelationGateUp
