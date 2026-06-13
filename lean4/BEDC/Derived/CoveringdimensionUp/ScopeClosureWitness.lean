import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionScopeClosureWitness [AskSetup] [PackageSetup]
    {K E C R O L H T P N compactRead coverRead refinementRead orderRead ledgerRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont K E compactRead →
        Cont compactRead C coverRead →
          Cont coverRead R refinementRead →
            Cont refinementRead O orderRead →
              Cont orderRead L ledgerRead →
                Cont ledgerRead N namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                            hsame row O ∨ hsame row L ∨ hsame row H ∨ hsame row T ∨
                              hsame row P ∨ hsame row N ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont K E compactRead ∧
                            Cont compactRead C coverRead ∧ Cont coverRead R refinementRead ∧
                              Cont refinementRead O orderRead ∧ Cont orderRead L ledgerRead ∧
                                Cont ledgerRead N namedRead ∧ PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory coverRead ∧
                        UnaryHistory refinementRead ∧ UnaryHistory orderRead ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute coverRoute refinementRoute orderRoute ledgerRoute namedRoute namedPkg
  obtain ⟨KUnary, EUnary, CUnary, RUnary, OUnary, LUnary, _HUnary, _TUnary, _PUnary,
    NUnary, _KECover, _CROrder, _OLReplay, _HTProvenance, _provenancePkg,
    _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed KUnary EUnary compactRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed compactUnary CUnary coverRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary RUnary refinementRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementUnary OUnary orderRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed orderUnary LUnary ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary NUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactRoute, coverRoute, refinementRoute, orderRoute, ledgerRoute,
            namedRoute, namedPkg⟩
    }
  · exact
      ⟨compactUnary, coverUnary, refinementUnary, orderUnary, ledgerUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
