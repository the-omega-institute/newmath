import BEDC.Derived.CompletionModulusCategoryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionModulusCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompletionModulusCategoryModulusFunctoriality [AskSetup] [PackageSetup]
    {O A S R D E F H C P N objectRead toleranceRead functorRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory O →
      UnaryHistory A →
        UnaryHistory S →
          UnaryHistory R →
            UnaryHistory D →
              UnaryHistory E →
                UnaryHistory F →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory P →
                        UnaryHistory N →
                          Cont O A objectRead →
                            Cont S R toleranceRead →
                              Cont toleranceRead D functorRead →
                                Cont functorRead F replayRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row replayRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row O ∨ hsame row A ∨ hsame row S ∨
                                              hsame row R ∨ hsame row D ∨ hsame row E ∨
                                                hsame row F ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨
                                                    hsame row N ∨ hsame row objectRead ∨
                                                      hsame row toleranceRead ∨
                                                        hsame row functorRead ∨
                                                          hsame row replayRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont O A objectRead ∧
                                              Cont S R toleranceRead ∧
                                                Cont toleranceRead D functorRead ∧
                                                  Cont functorRead F replayRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                          hsame ∧ UnaryHistory objectRead ∧
                                        UnaryHistory toleranceRead ∧
                                      UnaryHistory functorRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryO unaryA unaryS unaryR unaryD _unaryE unaryF _unaryH _unaryC _unaryP _unaryN
    objectRoute toleranceRoute functorRoute replayRoute provenancePkg namePkg
  have objectUnary : UnaryHistory objectRead :=
    unary_cont_closed unaryO unaryA objectRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryS unaryR toleranceRoute
  have functorUnary : UnaryHistory functorRead :=
    unary_cont_closed toleranceUnary unaryD functorRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed functorUnary unaryF replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row A ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row E ∨ hsame row F ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row objectRead ∨ hsame row toleranceRead ∨
                  hsame row functorRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O A objectRead ∧ Cont S R toleranceRead ∧
              Cont toleranceRead D functorRead ∧ Cont functorRead F replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, objectRoute, toleranceRoute, functorRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, objectUnary, toleranceUnary, functorUnary, replayUnary⟩

end BEDC.Derived.CompletionModulusCategoryUp
