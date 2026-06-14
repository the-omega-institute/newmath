import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RatCauchyGapWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RatCauchyGapWitnessNameCert_obligations [AskSetup] [PackageSetup]
    {L U D W R E H C P N lowerRead toleranceRead windowRead handoffRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory D ->
          UnaryHistory W ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory N ->
                  Cont L U lowerRead ->
                    Cont lowerRead D toleranceRead ->
                      Cont toleranceRead W windowRead ->
                        Cont windowRead R handoffRead ->
                          Cont handoffRead E sealRead ->
                            Cont sealRead N namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row L ∨ hsame row U ∨ hsame row D ∨
                                          hsame row W ∨ hsame row R ∨ hsame row E ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row lowerRead ∨
                                                hsame row toleranceRead ∨
                                                  hsame row windowRead ∨
                                                    hsame row handoffRead ∨
                                                      hsame row sealRead ∨
                                                        hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont L U lowerRead ∧
                                          Cont lowerRead D toleranceRead ∧
                                            Cont toleranceRead W windowRead ∧
                                              Cont windowRead R handoffRead ∧
                                                Cont handoffRead E sealRead ∧
                                                  Cont sealRead N namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory lowerRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory windowRead ∧ UnaryHistory handoffRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro unaryL unaryU unaryD unaryW unaryR unaryE unaryN lowerRoute toleranceRoute windowRoute
    handoffRoute sealRoute namedRoute pkgP pkgN
  have unaryLower : UnaryHistory lowerRead :=
    unary_cont_closed unaryL unaryU lowerRoute
  have unaryTolerance : UnaryHistory toleranceRead :=
    unary_cont_closed unaryLower unaryD toleranceRoute
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryTolerance unaryW windowRoute
  have unaryHandoff : UnaryHistory handoffRead :=
    unary_cont_closed unaryWindow unaryR handoffRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryHandoff unaryE sealRoute
  have unaryNamed : UnaryHistory namedRead :=
    unary_cont_closed unarySeal unaryN namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, unaryNamed⟩
  have core :
      NameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro namedRead sourceNamed
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lowerRead ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
                  hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U lowerRead ∧ Cont lowerRead D toleranceRead ∧
              Cont toleranceRead W windowRead ∧ Cont windowRead R handoffRead ∧
                Cont handoffRead E sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        have h₁ : hsame row sealRead ∨ hsame row namedRead := Or.inr source.left
        have h₂ : hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₁
        have h₃ :
            hsame row windowRead ∨ hsame row handoffRead ∨ hsame row sealRead ∨
              hsame row namedRead :=
          Or.inr h₂
        have h₄ :
            hsame row toleranceRead ∨ hsame row windowRead ∨ hsame row handoffRead ∨
              hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₃
        have h₅ :
            hsame row lowerRead ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
              hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₄
        have h₆ :
            hsame row N ∨ hsame row lowerRead ∨ hsame row toleranceRead ∨
              hsame row windowRead ∨ hsame row handoffRead ∨ hsame row sealRead ∨
                hsame row namedRead :=
          Or.inr h₅
        have h₇ :
            hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨ hsame row toleranceRead ∨
              hsame row windowRead ∨ hsame row handoffRead ∨ hsame row sealRead ∨
                hsame row namedRead :=
          Or.inr h₆
        have h₈ :
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
              hsame row toleranceRead ∨ hsame row windowRead ∨ hsame row handoffRead ∨
                hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₇
        have h₉ :
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row lowerRead ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
                hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₈
        have h₁₀ :
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row lowerRead ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
                hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₉
        have h₁₁ :
            hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row lowerRead ∨ hsame row toleranceRead ∨
                hsame row windowRead ∨ hsame row handoffRead ∨ hsame row sealRead ∨
                  hsame row namedRead :=
          Or.inr h₁₀
        have h₁₂ :
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
                hsame row toleranceRead ∨ hsame row windowRead ∨ hsame row handoffRead ∨
                  hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₁₁
        have h₁₃ :
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
                hsame row toleranceRead ∨ hsame row windowRead ∨ hsame row handoffRead ∨
                  hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₁₂
        have h₁₄ :
            hsame row U ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lowerRead ∨ hsame row toleranceRead ∨ hsame row windowRead ∨
                  hsame row handoffRead ∨ hsame row sealRead ∨ hsame row namedRead :=
          Or.inr h₁₃
        exact Or.inr h₁₄
      ledger_sound := by
        intro row source
        exact
          ⟨source.right, lowerRoute, toleranceRoute, windowRoute, handoffRoute, sealRoute,
            namedRoute, pkgP, pkgN⟩
    }
  exact
    ⟨cert, unaryLower, unaryTolerance, unaryWindow, unaryHandoff, unarySeal, unaryNamed⟩

end BEDC.Derived.RatCauchyGapWitnessUp
