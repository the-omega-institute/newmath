import BEDC.Derived.StreamMapUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamMapUp
namespace TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamMapNameCertObligationSurface [AskSetup] [PackageSetup]
    {S T F W Q D R H C P N sourceCell transportedCell targetCell outputCell tailRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    streamMapFields (StreamMapUp.mk S T F W Q D R H C P N) =
        [S, T, F, W, Q, D, R, H, C, P, N] →
      Cont S H sourceCell →
        Cont sourceCell F transportedCell →
          Cont transportedCell T targetCell →
            Cont targetCell W outputCell →
              Cont outputCell Q tailRead →
                Cont tailRead R sealRead →
                  PkgSig bundle sealRead pkg →
                    UnaryHistory S →
                      UnaryHistory H →
                        UnaryHistory F →
                          UnaryHistory T →
                            UnaryHistory W →
                              UnaryHistory Q →
                                UnaryHistory R →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row sealRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row S ∨ hsame row T ∨ hsame row F ∨
                                          hsame row W ∨ hsame row Q ∨ hsame row D ∨
                                            hsame row R ∨ hsame row H ∨ hsame row C ∨
                                              hsame row P ∨ hsame row N ∨
                                                hsame row sourceCell ∨
                                                  hsame row transportedCell ∨
                                                    hsame row targetCell ∨
                                                      hsame row outputCell ∨
                                                        hsame row tailRead ∨
                                                          hsame row sealRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont S H sourceCell ∧
                                          Cont sourceCell F transportedCell ∧
                                            Cont transportedCell T targetCell ∧
                                              Cont targetCell W outputCell ∧
                                                Cont outputCell Q tailRead ∧
                                                  Cont tailRead R sealRead ∧
                                                    PkgSig bundle sealRead pkg)
                                      hsame ∧ UnaryHistory sourceCell ∧
                                    UnaryHistory transportedCell ∧ UnaryHistory targetCell ∧
                                      UnaryHistory outputCell ∧ UnaryHistory tailRead ∧
                                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldsExact sourceRoute transportedRoute targetRoute outputRoute tailRoute sealRoute
    sealPkg unaryS unaryH unaryF unaryT unaryW unaryQ unaryR
  cases fieldsExact
  have sourceUnary : UnaryHistory sourceCell :=
    unary_cont_closed unaryS unaryH sourceRoute
  have transportedUnary : UnaryHistory transportedCell :=
    unary_cont_closed sourceUnary unaryF transportedRoute
  have targetUnary : UnaryHistory targetCell :=
    unary_cont_closed transportedUnary unaryT targetRoute
  have outputUnary : UnaryHistory outputCell :=
    unary_cont_closed targetUnary unaryW outputRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed outputUnary unaryQ tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryR sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨ hsame row Q ∨
              hsame row D ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceCell ∨ hsame row transportedCell ∨
                  hsame row targetCell ∨ hsame row outputCell ∨ hsame row tailRead ∨
                    hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S H sourceCell ∧ Cont sourceCell F transportedCell ∧
              Cont transportedCell T targetCell ∧ Cont targetCell W outputCell ∧
                Cont outputCell Q tailRead ∧ Cont tailRead R sealRead ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, transportedRoute, targetRoute, outputRoute, tailRoute,
          sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, sourceUnary, transportedUnary, targetUnary, outputUnary, tailUnary, sealUnary⟩

end TasteGate
end BEDC.Derived.StreamMapUp
