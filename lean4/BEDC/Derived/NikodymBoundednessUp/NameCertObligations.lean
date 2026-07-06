import BEDC.Derived.NikodymBoundednessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NikodymBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NikodymBoundednessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M A F W T B D R H C P N familyRead variationRead boundRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory A ->
        UnaryHistory F ->
          UnaryHistory W ->
            UnaryHistory T ->
              UnaryHistory B ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory P ->
                          UnaryHistory N ->
                            Cont M A familyRead ->
                              Cont F T variationRead ->
                                Cont variationRead B boundRead ->
                                  Cont C N nameRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row A ∨ hsame row F ∨
                                                hsame row W ∨ hsame row T ∨ hsame row B ∨
                                                  hsame row D ∨ hsame row R ∨ hsame row H ∨
                                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                      hsame row familyRead ∨
                                                        hsame row variationRead ∨
                                                          hsame row boundRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont M A familyRead ∧
                                                Cont F T variationRead ∧
                                                  Cont variationRead B boundRead ∧
                                                    Cont C N nameRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory familyRead ∧
                                            UnaryHistory variationRead ∧
                                              UnaryHistory boundRead ∧
                                                UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro MUnary AUnary FUnary _WUnary TUnary BUnary _DUnary _RUnary _HUnary CUnary
    PUnary NUnary familyRoute variationRoute boundRoute nameRoute provenancePkg namePkg
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed MUnary AUnary familyRoute
  have variationReadUnary : UnaryHistory variationRead :=
    unary_cont_closed FUnary TUnary variationRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed variationReadUnary BUnary boundRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed CUnary NUnary nameRoute
  have sourceAtName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N :=
    ⟨hsame_refl N, NUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row F ∨ hsame row W ∨ hsame row T ∨
              hsame row B ∨ hsame row D ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row familyRead ∨
                  hsame row variationRead ∨ hsame row boundRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M A familyRead ∧ Cont F T variationRead ∧
              Cont variationRead B boundRead ∧ Cont C N nameRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceAtName
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
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, familyRoute, variationRoute, boundRoute, nameRoute,
          provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, familyReadUnary, variationReadUnary, boundReadUnary, nameReadUnary⟩

end BEDC.Derived.NikodymBoundednessUp
