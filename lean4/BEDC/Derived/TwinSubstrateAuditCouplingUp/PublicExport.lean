import BEDC.Derived.TwinSubstrateAuditCouplingUp.NonCollapse

namespace BEDC.Derived.TwinSubstrateAuditCouplingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateAuditCouplingCarrier_public_export [AskSetup] [PackageSetup]
    {M G R L C H T P N metaRoute groundRoute pairedRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory L →
            UnaryHistory C →
              UnaryHistory H →
                Cont M R metaRoute →
                  Cont G R groundRoute →
                    Cont metaRoute L pairedRead →
                      Cont groundRoute C pairedRead →
                        Cont pairedRead H exportRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              PkgSig bundle pairedRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row exportRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row G ∨ hsame row R ∨
                                        hsame row L ∨ hsame row C ∨ hsame row H ∨
                                          hsame row T ∨ hsame row pairedRead ∨
                                            hsame row exportRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont M R metaRoute ∧
                                        Cont G R groundRoute ∧
                                          Cont metaRoute L pairedRead ∧
                                            Cont groundRoute C pairedRead ∧
                                              Cont pairedRead H exportRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro mUnary gUnary rUnary lUnary cUnary hUnary metaRouteCont groundRouteCont
    pairedFromMeta pairedFromGround exportRoute provenancePkg namePkg _pairedPkg
  have metaRouteUnary : UnaryHistory metaRoute :=
    unary_cont_closed mUnary rUnary metaRouteCont
  have _groundRouteUnary : UnaryHistory groundRoute :=
    unary_cont_closed gUnary rUnary groundRouteCont
  have pairedUnary : UnaryHistory pairedRead :=
    unary_cont_closed metaRouteUnary lUnary pairedFromMeta
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed pairedUnary hUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row R ∨ hsame row L ∨ hsame row C ∨
              hsame row H ∨ hsame row T ∨ hsame row pairedRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R metaRoute ∧ Cont G R groundRoute ∧
              Cont metaRoute L pairedRead ∧ Cont groundRoute C pairedRead ∧
                Cont pairedRead H exportRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metaRouteCont, groundRouteCont, pairedFromMeta, pairedFromGround,
          exportRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, exportUnary⟩

end BEDC.Derived.TwinSubstrateAuditCouplingUp
