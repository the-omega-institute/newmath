import BEDC.Derived.LayeredRelationGateUp.LedgerObligation

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LayeredRelationGate_obligation_closure [AskSetup] [PackageSetup]
    {A B L P N F G H C Pi sourceRead layerRead refusalRead verdictRead carrierRead
      classifierRead ledgerRead : BHist}
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
                        Cont P N refusalRead →
                          Cont refusalRead F verdictRead →
                            Cont verdictRead G carrierRead →
                              Cont P N classifierRead →
                                Cont layerRead F ledgerRead →
                                  PkgSig bundle Pi pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row carrierRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row A ∨ hsame row B ∨ hsame row L ∨
                                            hsame row P ∨ hsame row N ∨ hsame row F ∨
                                              hsame row G ∨ hsame row H ∨ hsame row C ∨
                                                hsame row Pi ∨ hsame row carrierRead ∨
                                                  hsame row classifierRead ∨
                                                    hsame row ledgerRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ PkgSig bundle Pi pkg)
                                        hsame ∧
                                      UnaryHistory carrierRead ∧
                                        UnaryHistory classifierRead ∧
                                          UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary bUnary lUnary pUnary nUnary fUnary gUnary piUnary sourceRoute layerRoute
    refusalRoute verdictRoute carrierRoute classifierRoute ledgerRoute packageEvidence
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
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed pUnary nUnary classifierRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed layerUnary fUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row carrierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row L ∨ hsame row P ∨ hsame row N ∨
              hsame row F ∨ hsame row G ∨ hsame row H ∨ hsame row C ∨ hsame row Pi ∨
                hsame row carrierRead ∨ hsame row classifierRead ∨ hsame row ledgerRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle Pi pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro carrierRead ⟨hsame_refl carrierRead, carrierUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageEvidence⟩
  }
  exact ⟨cert, carrierUnary, classifierUnary, ledgerUnary⟩

end BEDC.Derived.LayeredRelationGateUp
